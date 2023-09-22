-- Expand Zappa branching

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Printer (pp)
import CPSA.Lib.Entry
import CPSA.Lib.Expand (readSExprs)

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      sexprs <- readSExprs p
      h <- outputHandle output
      _ <- mapM (writeCpsaLn (pp margin defaultIndent) h) (map debranch sexprs)
      hClose h

writeCpsaLn :: (SExpr a -> String) -> Handle -> SExpr a -> IO ()
writeCpsaLn printer h sexpr =
    do
      hPutStrLn h $ printer sexpr
      hPutStrLn h ""

-- Type of an environment used for substitutions
type Env = [(String, SExpr Pos)]

-- Debranch a protocol and leave everything else alone.
debranch :: SExpr Pos -> SExpr Pos
debranch (L pos (S _ "defprotocol" : S _ name : S _ alg : xs)) =
    L pos (S pos "defprotocol" : S pos name : S pos alg :
             concatMap protBody xs)
debranch (L pos (S _ "defprotocol" : _)) =
    error (shows pos "Bad protocol")
debranch x = x

-- Debranch the body of a protocol focusing in on roles.
protBody :: SExpr Pos -> [SExpr Pos]
protBody (L pos (S _ "defrole" : S _ name : vars :
                   L _ (S _ "trace" : events) : alist)) =
    let traceEnvs = branchSplits events in
    if length traceEnvs == 1 then -- No branching in this role
        [defrole pos name vars (fst (head traceEnvs)) alist]
    else
        map f (zip [0..] traceEnvs)
        where
          f :: (Int, ([SExpr Pos], Env)) -> SExpr Pos
          f (i, (trace, env)) =
              defrole pos (name ++ show i) vars
                          (map (subst env) trace)
                          (map (g env) alist)
          g :: Env -> SExpr Pos -> SExpr Pos
          g env (L pos (s@(S _ _) : args)) =
              L pos (s : map (subst env) args)
          g _ x = x
protBody (L pos (S _ "defrole" : _)) =
    error (shows pos "Bad role")
protBody x = [x]

-- Find splits in a trace and return environments made from cheq's.
branchSplits :: [SExpr Pos] -> [([SExpr Pos], Env)]
branchSplits [] = [([], [])]
branchSplits [L _ (S _ "branch" : branches)] =
    ([], []) : concatMap f branches
    where
      f (L _ branch) = branchSplits branch
      f _ = [([], [])]
branchSplits (L _ [S _ "cheq", S _ var, term] : events) =
    map f (branchSplits events)
    where
      f (trace, env) = (trace, (var, term) : env)
branchSplits (event : events) =
    map f (branchSplits events)
    where
      f (trace, env) = (event : trace, env)

-- Construct a role from its parts.
defrole :: Pos -> String -> SExpr Pos -> [SExpr Pos] -> [SExpr Pos] -> SExpr Pos
defrole pos name vars trace alist =
    L pos (S pos "defrole" : S pos name : vars
                 : L pos (S pos "trace" : trace) : alist)

-- Substitute variables in a term when they are in an environment.
subst :: Env -> SExpr Pos -> SExpr Pos
subst env s@(S _ sym) =
    case lookup sym env of
      Just term -> term
      Nothing -> s
subst env (L pos (S _ fun : terms)) =
    L pos (S pos fun : map (subst env) terms)
subst _ x = x
