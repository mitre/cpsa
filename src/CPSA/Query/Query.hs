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
    | Null String
    | Member (SExpr Pos) String
    | HasChildren
    | HasDuplicates
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
              return (pq, ints)

parseQuery :: SExpr Pos -> IO Query
parseQuery (L _ [S _ "has-key", S _ sym]) =
    return (HasKey sym)
parseQuery (L _ [S _ "null", S _ sym]) =
    return (Null sym)
parseQuery (L _ [S _ "member", x, S _ sym]) =
    return (Member x sym)
parseQuery (L _ [S _ "has-children"]) =
    return HasChildren
parseQuery (L _ [S _ "has-duplicates"]) =
    return HasDuplicates
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
execQuery (q, []) ts =
    return (concatMap (execQueryTree q) ts)
execQuery (q, ints) ts =
    do
      ts <- mapM (getTree ts) (nub ints)
      return (concatMap (execQueryTree q) ts)

getTree :: Forest -> Int -> IO Tree
getTree _ int  | int < 0 = fail ("Bad tree index " ++ show int)
getTree ts int =
    loop ts int
    where
      loop [] _ = fail ("Cannot find tree " ++ show int)
      loop (t:_) 0 = return t
      loop (_:ts) i = loop ts (i - 1)

execQueryTree :: Query -> Tree -> [Int]
execQueryTree q t =
    ans ++ concatMap (execQueryTree q) (children t)
    where
      ans = if runQuery q t then [label (vertex t)] else []

runQuery :: Query -> Tree -> Bool
runQuery (HasKey sym) t =
    maybe False (const True) (assoc sym (alist (vertex t)))
runQuery (Null sym) t =
    maybe False null (assoc sym (alist (vertex t)))
runQuery (Member x sym) t =
    case assoc sym (alist (vertex t)) of
      Nothing -> False
      Just l -> elem x l
runQuery HasChildren t =
    not (null (children t))
runQuery HasDuplicates t =
    not (null (duplicates t))
runQuery (Not q) t = not (runQuery q t)
runQuery (And qs) t = all (\ q -> runQuery q t) qs
runQuery (Or qs) t = any (\ q -> runQuery q t) qs
