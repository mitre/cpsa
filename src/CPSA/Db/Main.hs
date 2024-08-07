-- Generate a database of facts from CPSA output

-- This programs loads CPSA output.  It assembles the skeletons in the
-- output into a forest of derivation trees.  It then prints the
-- forest in S-Expression syntax.  To be loadable by Prolog, the
-- output must be filtered through cpsa4dbprolog and then sorted so
-- that clauses of one predicate are colocated.

-- The output should be used by SWI Prolog as strings must not be atoms.
-- Load the generated file using consult/1.

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Signature (Sig, defaultSig, loadSig)
import CPSA.Algebra
import CPSA.Lib.Entry
import CPSA.Options
import CPSA.Db.Loader
import CPSA.Db.Tree
import CPSA.Db.Displayer

-- Algebra names
algs :: [String]
algs = [name, alias]

main :: IO ()
main =
    do
      let options = algOptions name
      let interp = algInterp name algs
      (p, (output, alg, margin)) <- start options interp
      h <- outputHandle output
      (_, ks) <- herald p margin h alg
      display h margin (forest $ reverse ks)
      hClose h

-- Handle the herald
herald :: PosHandle -> Int -> Handle -> String -> IO State
herald p margin h alg =
    do
      x <- readSExpr p
      case x of
        Nothing -> abort "Empty input"
        Just (L pos (S _ "herald" : name : xs)) ->
          do
            writeSExpr h margin (L pos [S pos "herald", name, L pos xs])
            hPutStrLn h ""
            sig <- loadSig pos (assoc "lang" xs)
            let nom = getAlgName xs alg
            select p margin h sig nom Nothing
        Just (L _ (S _ "comment" : _)) ->
          herald p margin h alg
        x ->
          select p margin h defaultSig alg x

select :: PosHandle -> Int -> Handle -> Sig ->
          String -> Maybe (SExpr Pos) -> IO State
select p margin h sig alg x =
    do
      writeComment h margin cpsaVersion
      writeComment h margin "CPSA Database"
      let stepper = step sig alg origin
      let state = ([], [])
      case () of
        _ | alg == name || alg == alias ->
            case x of
              Nothing -> go stepper p state
              Just x ->
                do
                  next <- stepper state x
                  go stepper p next
          | otherwise ->
               abort ("Bad algebra: " ++ alg)

go :: (a -> SExpr Pos -> IO a) -> PosHandle -> a -> IO a
go f p a =
    loop a
    where
      loop a =
          do
            x <- readSExpr p
            case x of
              Nothing ->
                  return a
              Just x ->
                  do
                    a <- f a x
                    loop a

getAlgName :: [SExpr a] -> String -> String
getAlgName xs name =
    case assoc "algebra" xs of
      [] -> name
      [S _ nom] -> nom
      _ -> error "Bad algbra field an herald"

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr a] -> [SExpr a]
assoc key alist =
    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]
