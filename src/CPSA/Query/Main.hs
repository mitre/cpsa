-- Reads and runs a query on a derivation tree.

-- This programs loads CPSA output and a query.  It assembles the
-- skeletons in the output into a forest of derivation trees.  It then
-- runs the query against the selected trees in the forest and returns
-- the labels of the skeletons that satisfy the query.

-- Each tree vertex is a skeleton represented as a S-Expression.
-- Information in the skeleton can be accessed by treating it as an
-- association list.  The query language allows one to ask questions
-- about the association list, such as if it has a given key.  For
-- example, you can list the shapes in a tree by asking if the
-- association list has the symbol "shape" as a key.

-- A query is a file containing S-Expressions.  The first S-Expression
-- contains the query proper, and the remaining S-Expressions are the
-- integers that select which trees in the forest will be the searched
-- by the query proper.  If there are no integers, the entire forest
-- is searched.  The syntax of the query proper is:

-- QUERY ::= (has-key SYMBOL)
--        |  (null SYMBOL)
--        |  (member SEXPR SYMBOL)
--        |  (has-children)
--        |  (has-duplicates)
--        |  (not QUERY)
--        |  (and QUERY*)
--        |  (or QUERY*)

-- The has-key predicate asks if SYMBOL is a key in a skeleton.  The
-- null? predicate asks if SYMBOL is a key and the value is the empty
-- list.  The member predicate asks if SEXPR is a member of the value
-- associated with key SYMBOL.  The has-children? predicate asks if
-- the current skeleton has children.  The has-duplicates? predicate
-- asks if the current skeleton has duplicates as descendents.  The
-- remaining operations implement the usual way to combine boolean
-- functions.

-- EXAMPLES
--
-- (has-key shape) 0 1
--
-- finds the skeletons in the first and second tree that have shape as
-- a key.  If this query is run against the test file output
-- tst/unilateral.txt, it will find that skeletons 1 and 3 are shapes.
--
-- (has-key aborted)
--
-- finds the skeletons in the forest that have aborted as a key.
-- If this query is run against the test file output
-- tst/wide-mouth-frog, it will find that skeleton 18 is aborted.

-- TRANSCRIPT
--
-- $ cat query.txt
-- (has-key shape) 0 1
-- $ cpsa4query query.txt tst/unilateral.txt
--     1    3

-- Usage: cpsa4query [OPTIONS] QUERY [FILE]
--   -o FILE  --output=FILE  output FILE
--   -m INT   --margin=INT   set output margin (default 72)
--   -h       --help         show help message
--   -v       --version      show version number

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import Numeric
import System.IO
import System.Console.GetOpt
import System.Environment
import Paths_cpsa
import Text.Printf (printf)
import CPSA.Lib.SExpr
import CPSA.Lib.Entry (abort, success, cpsaVersion, outputHandle)
import CPSA.Query.Loader
import CPSA.Query.Tree
import CPSA.Query.Query

main :: IO ()
main =
    do
      (query, p, (output, margin)) <- start filterOptions filterInterp
      ks <- loadPreskels p
      q <- loadQuery query
      ans <- execQuery q (forest ks)
      h <- outputHandle output
      showAns h margin ans
      hClose h

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

-- Load preskeletons
loadPreskels :: PosHandle -> IO ([Preskel])
loadPreskels h =
    do
      (_, k, s) <- loadFirst h
      ks <- loop [k] s
      return ks
    where
      loop ks s =
          do
            n <- loadNext s
            case n of
              Nothing ->        -- EOF
                  return $ reverse ks
              Just (k, s) ->
                  loop (k:ks) s

showAns :: Handle -> Int -> [Int] -> IO ()
showAns h margin ans =
    loop ans 0
    where
      loop [] 0 = return ()
      loop [] _ = hPutStrLn h ""
      loop (i:ints) col
          | col < margin =
              do
                let field = printf "%5d" i
                hPutStr h field
                loop ints (col + 5)
          | otherwise =
              do
                hPutStrLn h ""
                loop (i:ints) 0
