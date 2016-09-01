-- Summarize CPSA output as a formula in coherent logic

-- Copyright (c) 2011 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.CPSA
import CPSA.Lib.Entry
import CPSA.Lib.Options
import CPSA.SAS.SAS
import qualified CPSA.Basic.Algebra

-- Algebra names
algs :: [String]
algs = [CPSA.Basic.Algebra.name]

main :: IO ()
main =
    do
      let options = algOptions CPSA.Basic.Algebra.name
      let interp = algInterp CPSA.Basic.Algebra.name algs
      (p, (output, alg, margin)) <- start options interp
      h <- outputHandle output
      writeComment h margin cpsaVersion
      writeComment h margin "Coherent logic"
      case () of
        _ | alg == CPSA.Basic.Algebra.name ->
              go (step h alg CPSA.Basic.Algebra.origin margin)
                 p ([], [])
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

step :: Algebra t p g s e c => Handle ->
        String -> g -> Int -> State t g c ->
        Maybe (SExpr Pos) -> IO (State t g c)
step output _ _ margin state@([], []) (Just sexpr@(L _ (S _ cmt : _)))
     | cmt == "herald" || cmt == "comment" =
         do
           writeLnSExpr output margin sexpr
           return state
step output name origin margin state sexpr =
    do
      x <- tryIO (sas name origin state sexpr)
      case x of
        Right (acc, Nothing) ->
            after output margin acc sexpr
        Right (acc, Just x) ->
            do
              writeLnSExpr output margin x
              after output margin acc sexpr
        Left err ->
            abort (show err)

after :: Algebra t p g s e c => Handle -> Int -> State t g c ->
         Maybe (SExpr Pos) -> IO (State t g c)
after output margin state (Just sexpr@(L _ (S _ "defprotocol" : _))) =
    do
      writeLnSExpr output margin sexpr
      return state
after _ _ state _ =
    return state
