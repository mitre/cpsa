-- ZSL roles and protocols

module CPSA.ZSL.Protocol where

import CPSA.Lib.SExpr (SExpr(..), Pos)
import CPSA.Lib.Entry (abort)
import qualified CPSA.Algebra as A
import CPSA.ZSL.Term
import CPSA.ZSL.Event
import CPSA.ZSL.ZSL

-- A role parameterized by a type of body

data Role a = Role {
  rname :: !String,
  vars :: [SExpr Pos],
  body :: a,
  rest :: [SExpr Pos]
  }

type ZslRole = Role Stmt

type CpsaRole = Role Trace

-- Clear file positions from an S-expression

pos2Unit :: SExpr Pos -> SExpr ()
pos2Unit (S _ s) = S () s
pos2Unit (Q _ q) = Q () q
pos2Unit (N _ z) = N () z
pos2Unit (L _ l) = L () (map pos2Unit l)

-- Convert an input vars declaration into a list of (Var, Sort) pairs

toVarDecls :: [SExpr Pos] -> IO [(Var, Sort)]
toVarDecls sexprs = do
  pairs <- mapM A.loadVarPair sexprs
  foldl f (return []) (concat pairs)
  where
    f = \acc p -> acc >>= \ps -> g ps p
    g ps (S _ v, S _ sortStr) = sortOfStr sortStr >>= \sort -> return $ ((v, sort) : ps)
    g _ _ = abort "Failed to parse variable declarations"

-- Compile a ZSL role to its CPSA roles

toCpsaRoles :: ZslRole -> IO [CpsaRole]
toCpsaRoles (Role {rname=rname, vars=vars, body=body, rest=rest}) = do
  decls <- toVarDecls vars
  traces <- compute_traces (toSortMap decls) body
  return $ if length traces > 1 then map f (zip traces [1..]) else map g traces
  where
    f :: (Trace, Int) -> CpsaRole
    f (trace, i) = Role {rname=rname ++ show i, vars=vars, body=trace, rest=rest}
    g trace = Role {rname=rname, vars=vars, body=trace, rest=rest}

-- Convert an S-expression into a ZSL role

zslRoleOfSExpr :: SExpr Pos -> IO ZslRole
zslRoleOfSExpr (L _ (S _ "defrole" : S _ rname :
                     (L _ (S _ "vars" : vars)) :
                     (L _ (S _ "trace" : sexprs)) :
                     rest)) = do
  stmt <- stmtOfSExprs sexprs
  return $ Role {rname=rname, vars=vars, body=stmt, rest=rest}
zslRoleOfSExpr _ = abort "Failed to parse S-expression as ZSL role"

-- Convert a CPSA role into an S-expression

sexprOfCpsaRole :: CpsaRole -> SExpr ()
sexprOfCpsaRole (Role {rname=rname, vars=vars, body=body, rest=rest}) =
  L () (S () defrole : [vs, sexprOfTrace body] ++ map pos2Unit rest)
  where
    defrole = "defrole " ++ rname
    vs = L () (S () "vars" : map pos2Unit vars)

-- A protocol parameterized by a type of role

data Prot a = Prot {
  pname :: !String,
  alg :: !String,
  roles :: ![Role a]
  }

type ZslProt = Prot Stmt

type CpsaProt = Prot Trace

-- Compile a ZSL protocol to a CPSA protocol

toCpsaProt :: ZslProt -> IO CpsaProt
toCpsaProt (Prot {pname=pname, alg=alg, roles=zRoles}) =
  cRolesOpt >>= \cRoles -> return $ Prot {pname=pname, alg=alg, roles=cRoles}
  where
    cRolesOpt = foldl f (return []) zRoles
    f = \acc zRole -> acc >>= \cRoles -> g cRoles zRole
    g = \cRoles zRole -> toCpsaRoles zRole >>= \cRoles' -> return $ cRoles ++ cRoles'

-- Convert a list of S-expressions into a ZSL protocol

zslProtOfSExprs :: [SExpr Pos] -> IO ZslProt
zslProtOfSExprs (S _ pname : S _ alg : sexprs) = do
  roles <- mapM zslRoleOfSExpr sexprs
  return $ Prot {pname=pname, alg=alg, roles=roles}
zslProtOfSExprs _ = abort "Failed to parse S-expressions as a ZSL protocol"

-- Convert a CPSA protocol into an S-expression

sexprOfCpsaProt :: CpsaProt -> SExpr ()
sexprOfCpsaProt (Prot {pname=pname, alg=alg, roles=roles}) =
  L () (S () defprot : map sexprOfCpsaRole roles)
  where defprot = "defprotocol " ++ pname ++ " " ++ alg
