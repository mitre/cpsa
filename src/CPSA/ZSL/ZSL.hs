-- A source language for CPSA and Zappa

module CPSA.ZSL.ZSL where

import CPSA.Lib.SExpr (SExpr(..))
import CPSA.Lib.Entry (abort)
import CPSA.ZSL.Event
import CPSA.ZSL.Term

-- ZSL statements

data Stmt =
  Evnt Event
  | Cheq Var Term
  | Seqn Stmt Stmt
  | Brch [Stmt]
  deriving (Eq, Show)

-- Substitute a term for a variable in a statement

substStmt :: Var -> Term -> Stmt -> Stmt
substStmt v t (Evnt e)     = Evnt (substEvent v t e)
substStmt v t (Cheq v' t') = Cheq v' (substTerm t' v t)
substStmt v t (Seqn s1 s2) = Seqn (substStmt v t s1) (substStmt v t s2)
substStmt v t (Brch ss)    = Brch (map (substStmt v t) ss)

-- Determine whether a statement is well-formed relative to a sort map

stmtWf :: SortMap -> Stmt -> Bool
stmtWf m (Evnt e) = eventWf m e
stmtWf m (Cheq v t) =
  case (m v, sortOf m t) of
    (Just s, Just s') -> not (occursIn v t) && sortIncl s s'
    (_, _) -> False
stmtWf m (Seqn s1 s2) = stmtWf m s1 && stmtWf m s2
stmtWf m (Brch ss) = foldl (\b s -> b && stmtWf m s) True ss

-- Extend a trace with the result of compiling a statement (assumed to
-- be well-formed) in a particular environment, producing a list of
-- trace-environment pairs

extend_trace' :: Trace -> Env -> Stmt -> [(Trace, Env)]
extend_trace' trace env (Evnt e) = [(trace ++ [e], env)]
extend_trace' trace env (Cheq v t) = [(trace, env ++ [(v, t)])]
extend_trace' trace env (Seqn s1 s2) =
  let ext1 = extend_trace' trace env s1
  in concatMap (\x -> extend_trace' (fst x) (snd x) s2) ext1
extend_trace' trace env (Brch ss) =
  (trace, env) : concatMap (\s -> extend_trace' trace env s) ss

-- Check that a statement is well-formed relative to a sort map and,
-- if so, extend a trace with it

extend_trace :: SortMap -> Trace -> Env -> Stmt -> IO [(Trace, Env)]
extend_trace m trace env s =
  if stmtWf m s then return $ extend_trace' trace env s else abort "Failed to extend trace"

-- Compute the traces of a well-formed statement

compute_traces :: SortMap -> Stmt -> IO Traces
compute_traces m s =
  let f = \exts -> map (\x -> applyEnvTrace (snd x) (fst x)) exts
  in fmap f (extend_trace m [] [] s)

-- Convert a list of S-expressions into a statement

stmtOfSExprs :: [SExpr a] -> IO Stmt
stmtOfSExprs sexprs =
  case sexprs of
    [] -> abort "No S-expressions to parse as ZSL statement"
    [sexpr] -> f sexpr
    sexpr : sexprs -> do
      stmt <- f sexpr
      stmts <- stmtOfSExprs sexprs
      return $ Seqn stmt stmts
  where
    f (L _ [S _ "send", S _ ch, sexpr]) = do
      t <- termOfSExpr sexpr
      return $ Evnt (Send ch t)
    f (L _ [S _ "recv", S _ ch, sexpr]) = do
      t <- termOfSExpr sexpr
      return $ Evnt (Recv ch t)
    f (L _ [S _ "cheq", S _ v, sexpr]) = do
      t <- termOfSExpr sexpr
      return $ Cheq v t
    f (L _ (S _ "branch" : sexprs)) = do
      sexprs <- mapM flattenSExpr sexprs
      stmts <- mapM stmtOfSExprs sexprs
      return $ Brch stmts
    f _ = abort "Failed to parse S-expression as ZSL statement"
    flattenSExpr (L _ sexprs) = return sexprs
    flattenSExpr _ = abort "Malformed branch construct"
