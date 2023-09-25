-- Reads and runs a query on a derivation tree.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Query.Query (Query, loadQuery, execQuery) where

import System.IO
import Data.List (nub)
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Query.Tree
import CPSA.Query.Loader (Preskel (..), assoc)

data Query
    = HasKey String
    | Not Query
    | And [Query]
    | Or [Query]
    deriving Show

loadQuery :: String -> IO (Query, [Int])
loadQuery file =
    do
      input <- openFile file ReadMode
      p <- posHandle file input
      q <- readSExpr p
      case q of
        Nothing -> fail "no query in query input"
        Just x ->
            do
              pq <- parseQuery x
              ints <- getInts p
              case ints of
                [] -> fail "no ints in query input"
                _ -> return (pq, ints)

parseQuery :: SExpr Pos -> IO Query
parseQuery (L _ [S _ "has-key", S _ sym]) = return (HasKey sym)
parseQuery (L _ [S _ "not", x]) =
    do
      q <- parseQuery x
      return (Not q)
parseQuery (L _ (S _ "and" : xs)) =
    do
      qs <- mapM parseQuery xs
      return (And qs)
parseQuery (L _ (S _ "or" : xs)) =
    do
      qs <- mapM parseQuery xs
      return (Or qs)
parseQuery _ = fail "query does not parse"

getInts :: PosHandle -> IO [Int]
getInts p =
    do
      i <- readSExpr p
      case i of
        Nothing -> return []
        Just x ->
            case x of
              N _ n ->
                  do
                    rest <- getInts p
                    return (n:rest)
              _ -> fail "bad int in query file"

execQuery :: (Query, [Int]) -> Forest -> IO [Int]
execQuery (q, ints) ts =
    do
      ts <- mapM (getTree ts) (nub ints)
      return (concatMap (execQueryTree q) ts)

getTree :: Forest -> Int -> IO Tree
getTree [] int = fail ("Cannot find tree " ++ show int)
getTree (t:ts) int | label (vertex t) == int = return t
                   | otherwise = getTree ts int

execQueryTree :: Query -> Tree -> [Int]
execQueryTree q t =
    ans ++ concatMap (execQueryTree q) (children t)
    where
      ans = if runQuery q (vertex t) then [label (vertex t)] else []

runQuery :: Query -> Preskel -> Bool
runQuery (HasKey sym) k = maybe False (const True) (assoc sym (alist k))
runQuery (Not q) k = not (runQuery q k)
runQuery (And qs) k = all (\ q -> runQuery q k) qs
runQuery (Or qs) k = any (\ q -> runQuery q k) qs
