-- Compute the parameters of each protocol in the input

-- This module simply maps the function flow to S-expressions in the
-- file.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.CPSA
import CPSA.Lib.Entry
import CPSA.Parameters.Flow
import qualified CPSA.Basic.Algebra
import qualified CPSA.DiffieHellman.Algebra
import qualified CPSA.DiffieHellmanNoReciprocal.Algebra
import qualified CPSA.SimpleDiffieHellman.Algebra

-- Algebra names
algs :: [String]
algs = [CPSA.Basic.Algebra.name, CPSA.DiffieHellman.Algebra.name,
        CPSA.DiffieHellmanNoReciprocal.Algebra.name,
        CPSA.SimpleDiffieHellman.Algebra.name]

main :: IO ()
main =
    do
      let options = algOptions CPSA.Basic.Algebra.name
      let interp = algInterp CPSA.Basic.Algebra.name algs
      (p, (output, alg, margin)) <- start options interp
      h <- outputHandle output
      writeComment h margin cpsaVersion
      writeComment h margin "Protocols annotated with their parameters"
      case () of
        _ | alg == CPSA.Basic.Algebra.name ->
              go (step h alg CPSA.Basic.Algebra.origin margin) p
          | alg == CPSA.DiffieHellman.Algebra.name ->
              go (step h alg CPSA.DiffieHellman.Algebra.origin margin) p
          | alg == CPSA.DiffieHellmanNoReciprocal.Algebra.name ->
              go (step h alg
                       CPSA.DiffieHellmanNoReciprocal.Algebra.origin margin) p
          | alg == CPSA.SimpleDiffieHellman.Algebra.name ->
              go (step h alg CPSA.SimpleDiffieHellman.Algebra.origin margin) p
          | otherwise ->
               abort ("Bad algebra: " ++ alg)
      hClose h

go :: (SExpr Pos -> IO ()) -> PosHandle -> IO ()
go f p =
    loop
    where
      loop =
          do
            x <- readSExpr p
            case x of
              Nothing ->
                  return ()
              Just sexpr ->
                  do
                    f sexpr
                    loop

step :: Algebra t p g s e c => Handle ->
        String -> g -> Int -> SExpr Pos -> IO ()
step output name origin margin sexpr =
    do
      sexpr <- tryIO (dataFlow name origin sexpr)
      case sexpr of
        Right sexpr ->
            writeLnSEexpr output margin sexpr
        Left err ->
            abort (show err)
