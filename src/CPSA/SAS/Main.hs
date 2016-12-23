-- Summarize CPSA output as a formula in coherent logic

-- Copyright (c) 2011 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Lib.Entry
import CPSA.Options
import CPSA.SAS.SAS

-- Algebra names
algs :: [String]
algs = [name]

main :: IO ()
main =
    do
      let options = algOptions name
      let interp = algInterp name algs
      (p, (output, alg, margin)) <- start options interp
      h <- outputHandle output
      writeComment h margin cpsaVersion
      writeComment h margin "Coherent logic"
      case () of
        _ | alg == name ->
              go (step h alg origin margin)
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

step :: Handle -> String -> Gen -> Int -> State ->
        Maybe (SExpr Pos) -> IO State
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

after :: Handle -> Int -> State -> Maybe (SExpr Pos) -> IO State
after output margin state (Just sexpr@(L _ (S _ "defprotocol" : _))) =
    do
      writeLnSExpr output margin sexpr
      return state
after _ _ state _ =
    return state
