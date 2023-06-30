-- ZSL and CPSA source files

module CPSA.ZSL.Source (zslToCpsa) where

import CPSA.Lib.SExpr (SExpr(..), Pos)
import CPSA.Lib.Entry (abort)
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

toCpsaSrc :: ZslSrc -> IO CpsaSrc
toCpsaSrc (Src {defns=defns, prot=zProt}) =
  toCpsaProt zProt >>= \cProt -> return $ Src {defns=defns, prot=cProt}

-- Convert an S-expression into a ZSL source file

zslSrcOfSExprs :: [SExpr Pos] -> IO ZslSrc
zslSrcOfSExprs = f []
  where
    f _ [] = abort "No S-expressions to parse as ZSL source"
    f defns ((L _ (S _ "defprotocol" : sexprs)) : _) = do
      prot <- zslProtOfSExprs sexprs
      return $ Src {defns= reverse defns, prot=prot}
    f defns (sexpr : sexprs) = f (sexpr : defns) sexprs

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

-- Entry point for ZSL-to-CPSA translation

zslToCpsa :: [SExpr Pos] -> IO [SExpr ()]
zslToCpsa sexprs = do
  zslSrc <- zslSrcOfSExprs sexprs
  cpsaSrc <- toCpsaSrc zslSrc
  return $ sexprsOfCpsaSrc cpsaSrc
