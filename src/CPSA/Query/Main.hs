module Main (main) where

import System.IO
import System.Console.GetOpt
import System.Environment
import Paths_cpsa
import CPSA.Lib.SExpr
import CPSA.Lib.Entry (filterOptions, filterInterp, abort)



-- Returns the input query and S-expression and an interpretation of
-- the command line options.
start :: [OptDescr a] -> ([a] -> IO b) -> IO (String, PosHandle, b)
start options interp =
    do
      argv <- getArgs
      (flags, files) <- opts options argv
      opts <- interp flags
      (query, p) <- openInput options files
      return (query, p, opts)


opts :: [OptDescr a] -> [String] -> IO ([a], [String])
opts options argv =
    case getOpt RequireOrder options argv of
      (o, n, []) -> return (o, n)
      (_, _, errs) ->
          do
            msg <- usage options errs
            abort msg

openInput ::  [OptDescr a] -> [String] -> IO (String, PosHandle)
openInput _ [query, file] =
    do                          -- Input from named file
      input <- openFile file ReadMode
      p <- posHandle file input
      return (query, p)
openInput _ [query] =
    do
      p <- posHandle "" stdin          -- Input from the standard input
      return (query, p)
openInput options [] =
    do
      msg <- usage options ["no input files\n"]
      abort msg
openInput options _ =
    do
      msg <- usage options ["too many input files\n"]
      abort msg

usage :: [OptDescr a] -> [String] -> IO String  -- Return usage string
usage options errs =
    do
      name <- getProgName
      datadir <- getDataDir
      let header = "Usage: " ++ name ++ " [OPTIONS] QUERY [FILE]"
      let footer = "\nDocumentation directory: " ++ datadir
      return (concat errs ++ usageInfo header options ++ footer)
             
main :: IO ()
main =
    do
      (query, _, _) <- start filterOptions filterInterp
      putStrLn query
