-- Linear Diophantine Equation solver
--
-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

-- |
-- Module      : CPSA.DiffieHellmanNoReciprocal.LinDiophEq
-- Copyright   : (C) 2009 John D. Ramsdell
-- License     : BSD
--
-- Linear Diophantine Equation solver.
--
-- The solver uses the algorithm of Contejean and Devie as specified
-- in \"An Efficient Incremental Algorithm for Solving Systems of
-- Linear Diophantine Equations\", Information and Computation
-- Vol. 113, pp. 143-174, 1994.
--
-- The algorithm for systems of homogeneous linear Diophantine
-- equations follows.  Let e[k] be the kth basis vector for 1 <= k <=
-- n.  To find the minimal, non-negative solutions M to the system of
-- equations sum(i=1,n,a[i]*v[i]) = 0, the algorithm of Contejean and
-- Devie is:
--
--  1. [init] A := {e[k] | 1 <= k <= n}; M := {}
--
--  2. [new minimal results] M := M + {a in A | a is a solution}
--
--  3. [unnecessary branches] A := {a in A | all m in M : some
--     1 <= k <= n : m[k] < a[k]}
--
--  4. [breadth-first search] A := {a + e[k] | a in A, 1 <= k <= n,
-- \<sum(i=1,n,a[i]*v[i]),v[k]> \< 0}
--
--  5. [test] If A = {}, stop, else go to 2.
--
-- This module provides a solver for a single linear Diophantine
-- equation a*v = b, where a and v are vectors, not matrices.
--
-- When solving an inhomogeneous equation, it uses the homogeneous
-- solver after adding -b as the first element of v and by bounding
-- the first element of a to be one at each step in the computation.
-- The first element of a solution is zero if it is a solution to the
-- associated homogeneous equation, and one if it is a solution to the
-- inhomogeneous equation.
--
-- The algorithm is likely to be Fortenbacher's algorithm, the one
-- generalized to systems of equations by Contejean and Devie, but I
-- have not been able to verified this fact.

module CPSA.DiffieHellmanNoReciprocal.LinDiophEq (linDiophEq) where

import Data.Array
import Data.Set (Set)
import qualified Data.Set as S

{-- Debugging hack
import System.IO.Unsafe

z :: Show a => a -> b -> b
z x y = seq (unsafePerformIO (print x)) y

zz :: Show a => a -> a
zz x = z x x

pr :: Set (Vector Int) -> [[Int]]
pr s = map elems $ S.toList s

zzz :: Set (Vector Int) -> Set (Vector Int)
zzz s = z (pr s) s
--}

type Vector a = Array Int a

vector :: Int -> [a] -> Vector a
vector n elems =
    listArray (0, n - 1) elems

-- | The 'linDiophEq' function takes a list of integers that specifies
-- the coefficients of linear Diophantine equation and a constant,
-- and returns the equation's minimal, non-negative solutions.
--
-- When solving an inhomogeneous equation, the first element of a
-- solution is zero if it solves the associated homogeneous equation,
-- and one otherwise.
--
-- Thus to solve 2x + y - z = 2, use
--
-- @
-- linDiophEq [2,1,-1] 2 = [[0,0,1,1],[1,1,0,0],[0,1,0,2],[1,0,2,0]]
-- @
--
-- The two minimal solutions to the homogeneous equation are [0,1,1]
-- and [1,0,2], so any linear combinations of these solutions
-- contributes to a solution.  The solution that corresponds to
-- [1,0,0] is x = w + 1, y = v, and z = v + 2w.  The solution that
-- corresponds to [0,2,0] is x = w, y = v + 2, and z = v + 2w.

linDiophEq :: [Int] -> Int -> [[Int]]
linDiophEq [] _ = []
linDiophEq v 0 =
    newMinimalResults True (vector n v) (basis n) S.empty
    where n = length v
linDiophEq v c =
    newMinimalResults False (vector n (negate c:v)) (basis n) S.empty
    where n = 1 + length v

-- Construct the basis vectors for an n-dimensional space
basis :: Int -> Set (Vector Int)
basis n =
    S.fromList [ z // [(k, 1)] | k <- indices z ]
    where z = vector n $ replicate n 0

-- This is the main loop.

-- Add elements of a that solve the equation to m and the output
-- Variable hom is true when solving a homogeneous equation
newMinimalResults :: Bool -> Vector Int -> Set (Vector Int) ->
                     Set (Vector Int) -> [[Int]]
newMinimalResults _ _ a _ | S.null a = []
newMinimalResults hom v a m =
    loop m (S.toList a)         -- Test each element in a
    where
      loop m [] =               -- When done, prepare for next iteration
          let a' = unnecessaryBranches a m
              a'' = breadthFirstSearch hom v a' in
          newMinimalResults hom v a'' m
      loop m (x:xs)
           | prod v x == 0 && S.notMember x m =
               elems x:loop (S.insert x m) xs -- Answer found
           | otherwise =
               loop m xs

-- Breadth-first search using the algorithm of Contejean and Devie
-- Variable hom is true when solving a homogeneous equation
breadthFirstSearch :: Bool -> Vector Int ->
                      Set (Vector Int) -> Set (Vector Int)
breadthFirstSearch hom v a =
    S.fold f S.empty a
    where
      f x acc =
          foldl (flip S.insert) acc
            [ x // [(k, x!k + 1)] |
              k <- indices x,   -- When not hom, bound first element
              hom || k > 0 || x!k == 0, -- of x to be no more than one
              prod v x * v!k < 0 ] -- Fortenbacher contribution

-- Inner product
prod :: Vector Int -> Vector Int -> Int
prod x y =
    sum [ x!i * y!i | i <- indices x ]

-- Remove unnecessary branches.  A test vector is not necessary if all
-- of its elements are greater than or equal to the elements of some
-- minimal solution.
unnecessaryBranches :: Set (Vector Int) -> Set (Vector Int) -> Set (Vector Int)
unnecessaryBranches a m =
    S.filter f a
    where
      f x = all (g x) (S.toList m)
      g x y = not (lessEq y x)

-- Compare vectors element-wise.
lessEq :: Vector Int -> Vector Int -> Bool
lessEq x y =
    all (\i-> x!i <= y!i) (indices x)
