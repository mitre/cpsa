-- Provides a common entry point for programs based on the CPSA library.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Entry (start, usage, abort, success, defaultMargin,
                       defaultIndent, filterOptions, filterInterp,
                       readSExpr, gentlyReadSExpr, outputHandle,
                       writeSExpr, writeLnSExpr, cpsaVersion, comment,
                       writeComment, tryIO) where

import Numeric
import Control.Exception (try)
import System.IO
import System.IO.Error (ioeGetErrorString)
import System.Environment
import System.Console.GetOpt
import System.Exit
import Data.Version
import Paths_cpsa
import CPSA.Lib.SExpr
import CPSA.Lib.Printer

-- Returns the input S-expression and an interpretation of the command
-- line options.
start :: [OptDescr a] -> ([a] -> IO b) -> IO (PosHandle, b)
start options interp =
    do
      argv <- getArgs
      (flags, files) <- opts options argv
      opts <- interp flags
      p <- openInput options files
      return (p, opts)

opts :: [OptDescr a] -> [String] -> IO ([a], [String])
opts options argv =
    case getOpt RequireOrder options argv of
      (o, n, []) -> return (o, n)
      (_, _, errs) ->
          do
            msg <- usage options errs
            abort msg

openInput ::  [OptDescr a] -> [String] -> IO PosHandle
openInput _ [file] =
    do                          -- Input from named file
      input <- openFile file ReadMode
      posHandle file input
openInput _ [] =
    posHandle "" stdin          -- Input from the standard input
openInput options _ =
    do
      msg <- usage options ["too many input files\n"]
      abort msg

usage :: [OptDescr a] -> [String] -> IO String  -- Return usage string
usage options errs =
    do
      name <- getProgName
      datadir <- getDataDir
      let header = "Usage: " ++ name ++ " [OPTIONS] [FILE]"
      let footer = "\nDocumentation directory: " ++ datadir
      return (concat errs ++ usageInfo header options ++ footer)

-- Command line option flags
data Flag
    = Help                      -- Help
    | Info                      -- Version information
    | Margin String             -- Output line length
    | Output String             -- Output file name
      deriving Show

defaultMargin :: Int
defaultMargin = 72

filterOptions :: [OptDescr Flag]
filterOptions =
    [ Option ['o'] ["output"]  (ReqArg Output "FILE")  "output FILE",
      Option ['m'] ["margin"]  (ReqArg Margin "INT")
      ("set output margin (default " ++ show defaultMargin ++ ")"),
      Option ['h'] ["help"]    (NoArg Help)          "show help message",
      Option ['v'] ["version"] (NoArg Info)          "show version number" ]

-- Interpret option flags
filterInterp :: [Flag] -> IO (Maybe FilePath, Int)
filterInterp flags =
    loop flags Nothing defaultMargin
    where
      loop [] file margin =
          return (file, margin)
      loop (Output name : flags) Nothing margin =
          loop flags (Just name) margin
      loop (Margin value : flags) file _ =
          case readDec value of
            [(margin, "")] ->
                loop flags file margin
            _ ->
                do
                  msg <- usage filterOptions ["Bad value for margin\n"]
                  abort msg
      loop (Info : _) _ _ =
          success cpsaVersion
      loop (Help : _) _ _ =
          do                    -- Show help then exit with success
            msg <- usage filterOptions []
            success msg
      loop _ _ _ =
           do                   -- Show help then exit with failure
             msg <- usage filterOptions ["Bad option combination\n"]
             abort msg

-- Contruct the output handle specified by the command line.
outputHandle :: Maybe FilePath -> IO (Handle)
outputHandle output =
    case output of
      Nothing -> return stdout
      Just file -> openFile file WriteMode

abort :: String -> IO a         -- Print message then exit with failure
abort msg =
    do
      hPutStrLn stderr msg
      exitFailure

success :: String -> IO a       -- Print message then exit with success
success msg =
    do
      hPutStrLn stderr msg
      exitWith ExitSuccess

-- S-expression pretty print parameters
defaultIndent :: Int
defaultIndent = 2

writeSExpr :: Handle -> Int -> SExpr a -> IO ()
writeSExpr h margin sexpr =
    hPutStrLn h (pp margin defaultIndent sexpr)

writeLnSExpr :: Handle -> Int -> SExpr a -> IO ()
writeLnSExpr h margin sexpr =
    do
      hPutStrLn h ""
      writeSExpr h margin sexpr

cpsaVersion :: String
cpsaVersion = showString "CPSA " (showVersion version)

comment :: String -> SExpr ()
comment msg =
    L () [S () "comment", stringSExpr msg]

writeComment :: Handle -> Int -> String -> IO ()
writeComment h margin msg =
    writeSExpr h margin (comment msg)

-- Read an S-expression, and fail on error
readSExpr :: PosHandle -> IO (Maybe (SExpr Pos))
readSExpr p =
    do
      x <- tryIO (load p)
      case x of
        Right x ->
            return x
        Left err ->
            abort err

-- Read an S-expression, and gently fail on error by printing the
-- error message to standard error and returning EOF.
gentlyReadSExpr :: PosHandle -> IO (Maybe (SExpr Pos))
gentlyReadSExpr p =
    do
      x <- tryIO (load p)
      case x of
        Right x ->
            return x
        Left err ->
            do
              hPutStrLn stderr (show err)
              return Nothing

-- Exception handling for IO errors
tryIO :: IO a -> IO (Either String a)
tryIO x =
    do
      y <- try x
      case y of
        Right x ->
            return (Right x)
        Left err ->
            return (Left (ioeGetErrorString err))
