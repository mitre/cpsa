-- Main routine for ZSL to CPSA source translation

module Main (main) where

import Numeric
import System.IO
import System.Environment
import System.Console.GetOpt

import CPSA.Lib.SExpr
import CPSA.Lib.Expand
import CPSA.Lib.Entry
import CPSA.Algebra
import CPSA.Options
import CPSA.ZSL.Source

main :: IO ()
main = do
  argv <- getArgs
  (flags, files) <- opts options argv
  opts <- interp algs defaultOptions flags
  i <- openInput files
  zslSExprs <- readSExprs i
  cpsaSExprs <- zslToCpsa zslSExprs
  prettyPrint opts cpsaSExprs

opts :: [OptDescr a] -> [String] -> IO ([a], [String])
opts options argv =
    case getOpt RequireOrder options argv of
      (o, n, []) -> return (o, n)
      (_, _, errs) ->
          do
            msg <- usage options errs
            abort msg

openInput :: [String] -> IO PosHandle
openInput [file] =
    do                          -- Input from named file
      input <- openFile file ReadMode
      posHandle file input
openInput [] =
    posHandle "" stdin          -- Input from the standard input
openInput _ =
    do
      msg <- usage options ["too many input files\n"]
      abort msg

prettyPrint :: Options -> [SExpr a] -> IO ()
prettyPrint opts sexprs =
    do
      let m = optMargin opts
      h <- outputHandle (optFile opts)
      writeComment h m cpsaVersion
      writeComment h m "Expanded macros"
      mapM_ (writeLnSExpr h m) sexprs
      hClose h
      return ()

algs :: [String]
algs = [name, alias]

-- Command line option flags
data Flag
    = Output String             -- Output file name
    | Margin String             -- Output line length
    | Algebras                  -- Show algebras
    | Help                      -- Help
    | Info                      -- Version information
      deriving Show

options :: [OptDescr Flag]
options =
    [ Option ['o'] ["output"]   (ReqArg Output "FILE")  "output FILE",
      Option ['m'] ["margin"]   (ReqArg Margin "INT")
      ("set output margin (default " ++ show (optMargin defaultOptions) ++ ")"),
      Option ['s'] ["show-algebras"] (NoArg Algebras)  "show algebras",
      Option ['h'] ["help"]     (NoArg Help)      "show help message",
      Option ['v'] ["version"]  (NoArg Info)      "show version number" ]

-- Interpret option flags
interp :: [String] -> Options -> [Flag] -> IO Options
interp algs opts flags =
    loop flags opts
    where
      loop [] opts = return opts
      loop (Output name : flags) opts
          | optFile opts == Nothing =
              loop flags $ opts { optFile = Just name }
      loop (Margin value : flags) opts =
          case readDec value of
            [(margin, "")] ->
                loop flags $ opts { optMargin = margin }
            _ ->
                do
                  msg <- usage options ["Bad value for margin\n"]
                  abort msg
      loop (Algebras : _) _ =
          success $ unlines algs
      loop (Help : _) _ =
          do                    -- Show help then exit with success
            msg <- usage options []
            success msg
      loop (Info : _) _ =
          success cpsaVersion
      loop _ _ =
           do                   -- Show help then exit with failure
             msg <- usage options ["Bad option combination\n"]
             abort msg
