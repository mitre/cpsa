-- Makes the characteristic skeleton of a security goal

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Characteristic (characteristic) where

import Control.Monad
import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal
import CPSA.Lib.Strand

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

-- Entry point.  Takes a position, a protocol, a variable generator, a
-- goal, and a skeleton comment and makes a skeleton or fails.  This
-- function extracts the anecedent and univesally quantified variable.
characteristic :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                  g -> Goal t -> [SExpr ()] -> m (Preskel t g s e)
characteristic pos prot g goal kcomment =
  equalsForm pos prot g (uvars goal) (antec goal) kcomment

-- Checks for equals in an antecedent and fails if it finds one.  One
-- could use unification to solve the equality, and then apply the
-- result to the remaining parts of the formula.
equalsForm :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
           g -> [t] -> [AForm t] -> [SExpr ()] -> m (Preskel t g s e)
equalsForm pos _ _ _ as _ | any isEquals as =
  fail (shows pos "Equals not allowed in antecedent")
equalsForm pos prot g vars as kcomment =
  splitForm pos prot g vars as kcomment

isEquals :: AForm t -> Bool
isEquals (Equals _ _) = True
isEquals _ = False

-- Split the formula into instance formulas and skeleton formulas.
-- The instance formulas are used to generate the skeleton's
-- instances, and the skeleton formulas generate the rest.  Make the
-- instances, and then make the rest.
splitForm :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
           g -> [t] -> [AForm t] -> [SExpr ()] -> m (Preskel t g s e)
splitForm pos prot g vars as kcomment =
  do
    insts <- mkInsts pos prot g vars is
    mkSkel pos prot g vars insts ks kcomment
  where                         -- is is the instance formulas and
    (is, ks) = L.partition instForm as -- ks is the skeleton formulas

instForm :: AForm t -> Bool
instForm (RolePred _ _ _) = True
instForm (ParamPred _ _ _ _) = True
instForm (StrPrec _ _) = True
instForm _ = False

mkInsts :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
           g -> [t] -> [AForm t] -> m [Instance t e]
mkInsts _ _ _ _ _ = fail "bla"

-- Extracts the nodes from a list of variables.
nodes :: Algebra t p g s e c => [t] -> [t]
nodes vars = filter isNodeVar vars

-- Computes a map from nodes to indices
nodeIndices :: (Eq t, Monad m) => Pos -> [t] -> [AForm t] -> m [(t, Int)]
nodeIndices pos nodes as =
  mapM f nodes
  where
    f n =
      do
        i <- findNodeIndex pos n as
        return (n, i)

-- Find a node's index, and check for inconsistencies.
findNodeIndex :: (Eq t, Monad m) => Pos -> t -> [AForm t] -> m Int
findNodeIndex pos _ [] = fail (shows pos "Missing node index")
findNodeIndex pos n (RolePred _ i n' : as) | n == n' =
  checkNodeIndex pos n i as
findNodeIndex pos n (_ : as) =
  findNodeIndex pos n as

-- Check for inconsistencies.
checkNodeIndex :: (Eq t, Monad m) => Pos -> t -> Int -> [AForm t] -> m Int
checkNodeIndex _ _ i [] = return i
checkNodeIndex pos n i (RolePred _ i' n' : _) | n == n' && i /= i' =
  fail (shows pos "Incompatible node index")
checkNodeIndex pos n i (_ : as) =
  checkNodeIndex pos n i as

binNodes :: (Eq t, Monad m) => Pos -> [t] -> [(t, Int)] ->
            [AForm t] -> m [[t]]
binNodes pos nodes ni as =
  foldM f (map (\x -> [x]) nodes) as
  where
    f ns (StrPrec n n') =
      case (lookup n ni, lookup n' ni) of
        (Just i, Just i')
          | i >= i' ->
            fail (shows pos "Bad str-prec")
          | otherwise -> return $ merge n n' ns
        _ -> fail (shows pos "Bad lookup for str-prec")
    f ns _ = return ns

merge :: Eq t => t -> t -> [[t]] -> [[t]]
merge _ _ _ = []

mkSkel :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
          g -> [t] -> [Instance t e] -> [AForm t] ->
          [SExpr ()] -> m (Preskel t g s e)
mkSkel _ _ _ _ _ _ = fail "bla"
