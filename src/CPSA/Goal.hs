-- Security Goals

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Goal where

import CPSA.Algebra
import CPSA.Protocol

-- Syntax for the atomic formulas
data AForm
  = Length Role Term Int
  | Param Role Term Int Term Term -- role param first-height strand value
  | Prec NodeTerm NodeTerm
  | Non Term
  | Pnon Term
  | Uniq Term
  | UniqAt Term NodeTerm
  | AFact String [FactTerm]
  | Equals Term Term
  deriving Show

type NodeTerm = (Term, Int)

data FactTerm
  = FactNode NodeTerm
  | FactTerm Term
  deriving Show

data Goal
  = Goal { uvars :: [Term],          -- Universally quantified variables
           antec :: [AForm],         -- Antecedent
           concl :: [[AForm]] }      -- Conclusion

-- Ordering used to sort by constructor order.
aFormOrder :: AForm -> AForm -> Ordering
aFormOrder (Length _ _ _) (Length _ _ _) = EQ
aFormOrder (Length _ _ _) (Param _ _ _ _ _) = LT
aFormOrder (Length _ _ _) (Prec _ _) = LT
aFormOrder (Length _ _ _) (Non _) = LT
aFormOrder (Length _ _ _) (Pnon _) = LT
aFormOrder (Length _ _ _) (Uniq _) = LT
aFormOrder (Length _ _ _) (UniqAt _ _) = LT
aFormOrder (Length _ _ _) (AFact _ _) = LT
aFormOrder (Length _ _ _) (Equals _ _) = LT
aFormOrder (Param _ _ _ _ _) (Length _ _ _) = GT
aFormOrder (Param _ _ _ _ _) (Param _ _ _ _ _) = EQ
aFormOrder (Param _ _ _ _ _) (Prec _ _) = LT
aFormOrder (Param _ _ _ _ _) (Non _) = LT
aFormOrder (Param _ _ _ _ _) (Pnon _) = LT
aFormOrder (Param _ _ _ _ _) (Uniq _) = LT
aFormOrder (Param _ _ _ _ _) (UniqAt _ _) = LT
aFormOrder (Param _ _ _ _ _) (AFact _ _) = LT
aFormOrder (Param _ _ _ _ _) (Equals _ _) = LT
aFormOrder (Prec _ _) (Length _ _ _) = GT
aFormOrder (Prec _ _) (Param _ _ _ _ _) = GT
aFormOrder (Prec _ _) (Prec _ _) = EQ
aFormOrder (Prec _ _) (Non _) = LT
aFormOrder (Prec _ _) (Pnon _) = LT
aFormOrder (Prec _ _) (Uniq _) = LT
aFormOrder (Prec _ _) (UniqAt _ _) = LT
aFormOrder (Prec _ _) (AFact _ _) = LT
aFormOrder (Prec _ _) (Equals _ _) = LT
aFormOrder (Non _) (Length _ _ _) = GT
aFormOrder (Non _) (Param _ _ _ _ _) = GT
aFormOrder (Non _) (Prec _ _) = GT
aFormOrder (Non _) (Non _) = EQ
aFormOrder (Non _) (Pnon _) = LT
aFormOrder (Non _) (Uniq _) = LT
aFormOrder (Non _) (UniqAt _ _) = LT
aFormOrder (Non _) (AFact _ _) = LT
aFormOrder (Non _) (Equals _ _) = LT
aFormOrder (Pnon _) (Length _ _ _) = GT
aFormOrder (Pnon _) (Param _ _ _ _ _) = GT
aFormOrder (Pnon _) (Prec _ _) = GT
aFormOrder (Pnon _) (Non _) = GT
aFormOrder (Pnon _) (Pnon _) = EQ
aFormOrder (Pnon _) (Uniq _) = LT
aFormOrder (Pnon _) (UniqAt _ _) = LT
aFormOrder (Pnon _) (AFact _ _) = LT
aFormOrder (Pnon _) (Equals _ _) = LT
aFormOrder (Uniq _) (Length _ _ _) = GT
aFormOrder (Uniq _) (Param _ _ _ _ _) = GT
aFormOrder (Uniq _) (Prec _ _) = GT
aFormOrder (Uniq _) (Non _) = GT
aFormOrder (Uniq _) (Pnon _) = GT
aFormOrder (Uniq _) (Uniq _) = EQ
aFormOrder (Uniq _) (UniqAt _ _) = LT
aFormOrder (Uniq _) (AFact _ _) = LT
aFormOrder (Uniq _) (Equals _ _) = LT
aFormOrder (UniqAt _ _) (Length _ _ _) = GT
aFormOrder (UniqAt _ _) (Param _ _ _ _ _) = GT
aFormOrder (UniqAt _ _) (Prec _ _) = GT
aFormOrder (UniqAt _ _) (Non _) = GT
aFormOrder (UniqAt _ _) (Pnon _) = GT
aFormOrder (UniqAt _ _) (Uniq _) = GT
aFormOrder (UniqAt _ _) (UniqAt _ _) = EQ
aFormOrder (UniqAt _ _) (AFact _ _) = LT
aFormOrder (UniqAt _ _) (Equals _ _) = LT
aFormOrder (AFact _ _) (Length _ _ _) = GT
aFormOrder (AFact _ _) (Param _ _ _ _ _) = GT
aFormOrder (AFact _ _) (Prec _ _) = GT
aFormOrder (AFact _ _) (Non _) = GT
aFormOrder (AFact _ _) (Pnon _) = GT
aFormOrder (AFact _ _) (Uniq _) = GT
aFormOrder (AFact _ _) (UniqAt _ _) = GT
aFormOrder (AFact _ _) (AFact _ _) = EQ
aFormOrder (AFact _ _) (Equals _ _) = LT
aFormOrder (Equals _ _) (Length _ _ _) = GT
aFormOrder (Equals _ _) (Param _ _ _ _ _) = GT
aFormOrder (Equals _ _) (Prec _ _) = GT
aFormOrder (Equals _ _) (Non _) = GT
aFormOrder (Equals _ _) (Pnon _) = GT
aFormOrder (Equals _ _) (Uniq _) = GT
aFormOrder (Equals _ _) (UniqAt _ _) = GT
aFormOrder (Equals _ _) (AFact _ _) = GT
aFormOrder (Equals _ _) (Equals _ _) = EQ

aFreeVars :: [Term] -> AForm -> [Term]
aFreeVars vars (Length _ z _) = addVars vars z
aFreeVars vars (Param _ _ _ z t) = addVars (addVars vars z) t
aFreeVars vars (Prec (x, _) (y, _)) = addVars (addVars vars x) y
aFreeVars vars (Non t) = addVars vars t
aFreeVars vars (Pnon t) = addVars vars t
aFreeVars vars (Uniq t) = addVars vars t
aFreeVars vars (UniqAt t (z, _)) = addVars (addVars vars t) z
aFreeVars vars (AFact _ ft) =
  foldl f vars ft
  where
    f vars (FactNode (z, _)) = addVars vars z
    f vars (FactTerm t) = addVars vars t
aFreeVars vars (Equals x y) = addVars (addVars vars x) y
