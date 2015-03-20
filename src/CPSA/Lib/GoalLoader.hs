-- Loads security goals from S-expressions.

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.GoalLoader (loadSentence) where

import Control.Monad
import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

loadSentence :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                g -> SExpr Pos -> m (g, Goal t)
loadSentence _ prot g (L pos [S _ "forall", L _ vs, x]) =
  do
    (g, vars) <- loadVars g vs
    loadImplication pos prot g vars x
loadSentence pos _ _ _ = fail (shows pos "Bad goal sentence")

loadImplication :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                   g -> [t] -> SExpr Pos -> m (g, Goal t)
loadImplication _ prot g vars (L pos [S _ "implies", a, c]) =
  do
    (g, antec) <- loadRoleSpecific pos prot g vars a
    return (g, Goal { antec = antec, concl = [] })

loadRoleSpecific :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                    g -> [t] -> SExpr Pos -> m (g, [AForm t])
loadRoleSpecific pos prot g vars x =
  do
    (g, as) <- loadConjunction pos prot g vars x
    let as' = L.sortBy (\(_, x) (_, y) -> aFormOrder x y) as
    foldM_ roleSpecific vars as'
    return (g, map snd as')

loadConjunction :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                   [t] -> g -> SExpr Pos -> m (g, [(Pos, AForm t)])
loadConjunction _ p kvars g nvm (L pos (S _ "and" : xs)) =
  loadConjuncts pos p kvars g nvm xs []
loadConjunction top p kvars g nvm x =
  do
    (g, pos, a) <- loadPrimary top p kvars g nvm x
    return (g, [(pos, a)])

loadConjuncts :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                 [t] -> g -> [SExpr Pos] -> [(Pos, AForm t)] ->
                 m (g, [(Pos, AForm t)])
loadConjuncts _ _ _ g [] rest = return (g, reverse rest)
loadConjuncts top p kvars g (x : xs) rest =
  do
    (g, pos, a) <- loadPrimary top p kvars g x
    loadConjuncts top p kvars g xs ((pos, a) : rest)

loadPrimary :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
               [t] -> g -> SExpr Pos -> m (g, Pos, AForm t)
loadPrimary _ _ kvars g (L pos [S _ "=", x, y]) =
  do
    (g, t) <- loadSgTerm kvars g x
    (g, t') <- loadSgTerm kvars g y
    return (g, pos, Equals t t')
loadPrimary _ _ kvars g (L pos [S _ "non", x]) =
  do
    t <- loadAlgTerm kvars x
    return (g, pos, Non t)
loadPrimary _ _ kvars g (L pos [S _ "pnon", x]) =
  do
    t <- loadAlgTerm kvars x
    return (g, pos, Pnon t)
loadPrimary _ _ kvars g (L pos [S _ "uniq-at", x, y]) =
  do
    t <- loadAlgTerm kvars x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, UniqAt t t')
loadPrimary _ _ kvars g (L pos [S _ "str-prec", x, y]) =
  do
    (g, t) <- loadNodeTerm kvars g x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, StrPrec t t')
loadPrimary _ _ kvars g (L pos [S _ "prec", x, y]) =
  do
    (g, t) <- loadNodeTerm kvars g x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, Prec t t')
loadPrimary _ p kvars g (L pos [S _ "p", Q _ name, N _ i, x]) =
  do
    r <- lookupRole pos p name
    (g, t) <- loadNodeTerm kvars g x
    case i < 0 || i >= length (rtrace r) of
      True -> fail (shows pos "Bad index")
      False -> return (g, pos, RolePred r i t)
loadPrimary _ p kvars g (L pos [S _ "p", Q _ name, Q var x, y, z]) =
  do
    r <- lookupRole pos p name
    v <- loadAlgTerm (rvars r) (S var x)
    (g, n) <- loadNodeTerm kvars g y
    t <- loadAlgTerm kvars z
    case isVar v of
      False -> fail (shows pos "Bad parameter -- not a variable")
      True -> return (g, pos, ParamPred r v n t)
loadPrimary pos _ _ _ _ = fail (shows pos "Bad formula")

loadNodeTerm :: (Algebra t p g s e c, Monad m) => [t] -> g ->
                SExpr Pos -> m (g, t)
loadNodeTerm ts g x =
  do
    (g, t) <- loadSgTerm ts g x
    case isNodeVar t of
      True -> return (g, t)
      False -> fail (shows (annotation x) "Expecting a node variable")

loadAlgTerm :: (Algebra t p g s e c, Monad m) => [t] -> SExpr Pos -> m t
loadAlgTerm _ x@(L _ [N _ _, N _ _]) =
  fail (shows (annotation x) "Expecting an algebra term")
loadAlgTerm ts x =
  do
    t <- loadTerm ts x
    case isNodeVar t of
      True -> fail (shows (annotation x) "Expecting an algebra term")
      False -> return t

loadSgTerm :: (Algebra t p g s e c, Monad m) => [t] -> g ->
              SExpr Pos -> m (g, t)
loadSgTerm _ ts g x =
  do
    t <- loadTerm ts x
    return (g, t)

-- Role specific check

termVars :: Algebra t p g s e c => t -> [t]
termVars t = addVars [] t

allBound :: Algebra t p g s e c => [t] -> t -> Bool
allBound unbound t =
  L.all (flip L.notElem unbound) (termVars t)

roleSpecific :: (Algebra t p g s e c, Monad m) =>
                [t] -> (Pos, AForm t) -> m [t]
roleSpecific unbound (_, RolePred _ _ n) =
  return $ L.delete n unbound
roleSpecific unbound (pos, ParamPred _ _ n t)
  | L.notElem n unbound = return $ unbound L.\\ termVars t
  | otherwise = fail (shows pos "Unbound variable in parameter predicate")
roleSpecific unbound (pos, StrPrec n n')
  | L.notElem n unbound && L.notElem n' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in str-prec")
roleSpecific unbound (pos, Prec n n')
  | L.notElem n unbound && L.notElem n' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in prec")
roleSpecific unbound (pos, Non t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in non")
roleSpecific unbound (pos, Pnon t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in pnon")
roleSpecific unbound (pos, UniqAt t n)
  | allBound unbound t && L.notElem n unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in uniq-at")
roleSpecific unbound (pos, Equals t t')
  | isNodeVar t && isNodeVar t' =
    case L.notElem t unbound && L.notElem t' unbound of
      True -> return unbound
      False -> fail (shows pos "Unbound variable in equals")
  | isNodeVar t = fail (shows pos "Type mismatch in equals")
  | isNodeVar t' = fail (shows pos "Type mismatch in equals")
  | allBound unbound t && allBound unbound t' = return unbound
  | otherwise = fail (shows pos "Unbound variable in equals")

