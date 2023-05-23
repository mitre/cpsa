module CPSA.Options (Options(..), defaultOptions,
                     algOptions, algInterp) where

import Numeric
import System.Console.GetOpt
import CPSA.Lib.Entry
import CPSA.Algebra (name)

-- CPSA options and default values

data Options = Options {
      optFile :: Maybe FilePath, -- Nothing specifies standard output
      optAlg :: String,          -- Name of the algebra
      optAnalyze :: Bool,        -- False when only expanding macros
      optNoIsoChk :: Bool, -- True when not performing isomorphism checks
      optCheckNoncesFirst :: Bool, -- True when checking nonces first
      optTryOldStrandsFirst :: Bool, -- True when visiting old strands first
      optTryYoungNodesFirst :: Bool, -- True when visiting young nodes first
      optGoalsSat :: Bool , -- True when goals satisfied stops tree expansion
      optLimit :: Int,          -- Step count limit
      optBound :: Int,          -- Strand cound bound
      optDepth :: Int,          -- Tree depth bound
      optMargin :: Int,         -- Output line length
      optIndent :: Int }        -- Pretty printing indent
    deriving Show

defaultOptions :: Options
defaultOptions = Options {
  optFile = Nothing,
  optAlg = name,
  optAnalyze = True,
  optNoIsoChk = False,
  optCheckNoncesFirst = False,
  optTryOldStrandsFirst = False,
  optTryYoungNodesFirst = False,
  optGoalsSat = False,
  optLimit = 2000,
  optBound = 12,
  optDepth = 0,                 -- Infinite
  optMargin = 72,
  optIndent = 2 }

-- Command line option flags
data Flag
    = Help                      -- Help
    | Info                      -- Version information
    | Algebra String            -- Algebra
    | Algebras                  -- Show algebras
    | Margin String             -- Output line length
    | Output String             -- Output file name
      deriving Show

algOptions :: String -> [OptDescr Flag]
algOptions defaultAlgebra =
    [ Option ['o'] ["output"]  (ReqArg Output "FILE")  "output FILE",
      Option ['m'] ["margin"]  (ReqArg Margin "INT")
      ("set output margin (default " ++ show (optMargin defaultOptions) ++ ")"),
      Option ['a'] ["algebra"]  (ReqArg Algebra "STRING")
      ("algebra (default " ++ defaultAlgebra ++ ")"),
      Option ['s'] ["show-algebras"] (NoArg Algebras)  "show algebras",
      Option ['h'] ["help"]    (NoArg Help)          "show help message",
      Option ['v'] ["version"] (NoArg Info)          "show version number" ]

data Params = Params
    { file :: Maybe FilePath,   -- Nothing specifies standard output
      alg :: String,            -- Name of the algebra
      margin :: Int }           -- Output line length
    deriving Show

-- Interpret option flags
algInterp :: String -> [String] -> [Flag] -> IO (Maybe FilePath, String, Int)
algInterp alg algs flags =
    loop flags (Params { file = Nothing, alg = alg,
                         margin = optMargin defaultOptions })
    where
      loop [] (Params { file = file, alg = alg, margin = margin}) =
          return (file, alg, margin)
      loop (Output name : flags)  params
          | file params == Nothing =
              loop flags $ params { file = Just name }
      loop (Margin value : flags) params =
          case readDec value of
            [(margin, "")] ->
                loop flags $ params { margin = margin }
            _ ->
                do
                  msg <- usage (algOptions alg) ["Bad value for margin\n"]
                  abort msg
      loop (Algebra name : flags) params
          | elem name algs = loop flags $ params { alg = name }
          | otherwise =
              abort ("Algebra " ++ name ++ " not one of\n" ++ unlines algs)
      loop (Algebras : _) _ =
          success $ unlines algs
      loop (Info : _) _ =
          success cpsaVersion
      loop (Help : _) _ =
          do                    -- Show help then exit with success
            msg <- usage (algOptions alg) []
            success msg
      loop _ _ =
           do                   -- Show help then exit with failure
             msg <- usage (algOptions alg) ["Bad option combination\n"]
             abort msg
