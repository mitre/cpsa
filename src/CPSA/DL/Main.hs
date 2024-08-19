-- Translates a query in dynamic logic into Prolog.

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Lib.Pretty
import CPSA.DL.Structs
import CPSA.DL.Loader
import CPSA.DL.Simplifier
import CPSA.DL.Prolog
import CPSA.DL.Compiler

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      h <- outputHandle output
      hPutStrLn h "%% Dynamic Logic"
      hPutStrLn h ""
      let (g, k) = freshId origin "K" Intr
      loop h margin k g p
      hClose h

loop :: Handle -> Int -> Id -> Gen -> PosHandle -> IO ()
loop h m k g p =
    do
      x <- readSExpr p
      case x of
        Nothing ->
            return ()
        Just x ->
            do
              (g', q) <- loadQuery g x
              (g'', pl) <- compileQuery k g' (simplify q)
              display h m (map pretty pl)
              loop h m k g'' p

display :: Handle -> Int -> [Pretty] -> IO ()
display _ _ [] =
    return ()
display h m (p : ps) =
    do
      hPutStrLn h ""
      hPutStrLn h (pr m p "")
      display h m ps
