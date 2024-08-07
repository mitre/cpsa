-- Translates a query in dynamic logic into Prolog.

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

-- import System.IO
-- import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.DL.Structs
import CPSA.DL.Loader

main :: IO ()
main =
    do
      (p, (_, _)) <- start filterOptions filterInterp
      x <- readSExpr p
      case x of
        Nothing ->
            abort "No input"
        Just x ->
            do
              (_, _) <- loadQuery origin x
              return ()
