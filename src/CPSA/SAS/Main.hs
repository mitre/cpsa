-- Summarize CPSA output as a formula in coherent logic

-- Copyright (c) 2011 The MITRE Corporation
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
import CPSA.SAS.SAS

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
      -- Handle the herald
      x <- readSExpr p
      case x of
        Nothing -> abort "Empty input"
        Just x@(L pos (S _ "herald" : _ : xs)) ->
          do
            writeSExpr h margin x
            hPutStrLn h ""
            sig <- loadSig pos (assoc "lang" xs)
            let nom = getAlgName xs alg
            select p margin h sig nom Nothing
        x ->
          select p margin h defaultSig alg x

select :: PosHandle -> Int -> Handle -> Sig ->
          String -> Maybe (SExpr Pos) -> IO ()
select p margin h sig alg x =
    do
      writeComment h margin cpsaVersion
      writeComment h margin "Coherent logic"
      let stepper = step h alg origin margin
      let state = (sig, [], [])
      case () of
        _ | alg == name || alg == alias ->
            case x of
              Nothing -> go stepper p state
              _ ->
                do
                  next <- stepper state x
                  go stepper p next
          | otherwise ->
               abort ("Bad algebra: " ++ alg)
      hClose h

go :: (a -> Maybe (SExpr Pos) -> IO a) -> PosHandle -> a -> IO ()
go f p a =
    loop a
    where
      loop a =
          do
            x <- readSExpr p
            case x of
              Nothing ->
                  do
                    _ <- f a x
                    return ()
              Just _ ->
                  do
                    a <- f a x
                    loop a

step :: Handle -> String -> Gen -> Int -> State ->
        Maybe (SExpr Pos) -> IO State
step output _ _ margin state@(_, [], [])
     (Just sexpr@(L _ (S _ "comment" : _))) =
    do
      writeLnSExpr output margin sexpr
      return state
step output name origin margin state sexpr =
    do
      x <- tryIO (sas name origin state sexpr)
      case x of
        Left err ->
            abort err
        Right (acc, Nothing) ->
            after output margin acc sexpr
        Right (acc, Just x) ->
            do
              writeLnSExpr output margin x
              after output margin acc sexpr

after :: Handle -> Int -> State -> Maybe (SExpr Pos) -> IO State
after output margin state (Just sexpr@(L _ (S _ "defprotocol" : _))) =
    do
      writeLnSExpr output margin sexpr
      return state
after _ _ state _ =
    return state

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
