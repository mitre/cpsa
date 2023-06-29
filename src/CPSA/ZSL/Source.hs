-- ZSL and CPSA source files

module CPSA.ZSL.Source where

import CPSA.Lib.SExpr (SExpr(..), Pos)
import CPSA.ZSL.Event
import CPSA.ZSL.ZSL
import CPSA.ZSL.Protocol

-- A protocol source file

data Src a = Src {
  defns :: [SExpr Pos],
  prot :: Prot a
  }

type ZslSrc = Src Stmt

type CpsaSrc = Src Trace

-- Translate a ZSL source file into a CPSA source file

toCpsaSrc :: ZslSrc -> Maybe CpsaSrc
toCpsaSrc (Src {defns=defns, prot=zProt}) =
  toCpsaProt zProt >>= \cProt -> Just (Src {defns=defns, prot=cProt})

-- Generate a herald as an S-expression from a given protocol name and
-- algebra

mkHerald :: String -> String -> SExpr ()
mkHerald name alg =
  L () [S () "herald", S () ("\"" ++ name ++ "\""), a]
  where a = L () [S () "algebra", S () alg]

-- Convert a CPSA source file into a list of S-expressions

sexprsOfCpsaSrc :: CpsaSrc -> [SExpr ()]
sexprsOfCpsaSrc (Src {defns=defns, prot=prot@(Prot {pname=pname, alg=alg, roles=_})}) =
  mkHerald pname alg : map pos2Unit defns ++ [sexprOfCpsaProt prot]
