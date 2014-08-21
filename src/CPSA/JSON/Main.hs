-- Pretty print the input

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import Numeric
import System.IO
import System.Console.GetOpt
import CPSA.Lib.CPSA
import CPSA.Lib.Entry

-- Runtime parameters

data Params = Params
    { file :: Maybe FilePath,   -- Nothing specifies standard output
      prefix :: Bool,           -- Use prefix notation?
      margin :: Int }           -- Output line length
    deriving Show

indent :: Int
indent = optIndent defaultOptions

main :: IO ()
main =
    do
      (p, params) <- start options interp
      h <- outputHandle $ file params
      let printer = if prefix params then pp else printItem
      go (writeCpsaLn (printer (margin params) indent) h) p
      hClose h

writeCpsaLn :: (SExpr a -> String) -> Handle -> SExpr a -> IO ()
writeCpsaLn printer h sexpr =
    do
      hPutStrLn h $ printer sexpr
      hPutStrLn h ""

go :: (SExpr Pos -> IO ()) -> PosHandle -> IO ()
go f p =
    loop
    where
      loop =
          do
            x <- gentlyReadSExpr p
            case x of
              Nothing ->
                  return ()
              Just sexpr ->
                  do
                    f sexpr
                    loop

-- Command line option flags
data Flag
    = Help                      -- Help
    | Info                      -- Version information
    | Margin String             -- Output line length
    | Infix                     -- Select output notation
    | Output String             -- Output file name
      deriving Show

defaultMargin :: Int
defaultMargin = optMargin defaultOptions

options :: [OptDescr Flag]
options =
    [ Option ['o'] ["output"]   (ReqArg Output "FILE") "output FILE",
      Option ['m'] ["margin"]   (ReqArg Margin "INT")
      ("set output margin (default " ++ show defaultMargin ++ ")"),
      Option ['i'] ["infix"]    (NoArg Infix)  "output uses infix notation",
      Option ['h'] ["help"]     (NoArg Help)           "show help message",
      Option ['v'] ["version"]  (NoArg Info)           "show version number" ]

-- Interpret option flags
interp :: [Flag] -> IO Params
interp flags =
    loop flags (Params { file = Nothing, -- By default, no output file
                         prefix = True,
                         margin = defaultMargin })
    where
      loop [] params = return params
      loop (Output name : flags) params
          | file params == Nothing =
              loop flags $ params { file = Just name }
      loop (Infix : flags) params =
          loop flags $ params { prefix = False }
      loop (Margin value : flags) params =
          case readDec value of
            [(margin, "")] ->
                loop flags $ params { margin = margin }
            _ ->
                do
                  msg <- usage options ["Bad value for margin\n"]
                  abort msg
      loop (Info : _) _ =
          success cpsaVersion
      loop (Help : _) _ =
          do                    -- Show help then exit with success
            msg <- usage options []
            success msg
      loop _ _ =
           do                   -- Show help then exit with failure
             msg <- usage options ["Bad option combination\n"]
             abort msg
