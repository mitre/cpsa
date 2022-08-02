-- Contains generic list functions and a function that determines if a
-- graph has a cycle.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Utilities where

import qualified Data.Set as S
import qualified Data.List as L
import Data.List (foldl')

adjoin :: Eq a => a -> [a] -> [a]
adjoin x xs
    | x `elem` xs = xs
    | otherwise = x : xs

-- Delete the nth item in a list
deleteNth :: Int -> [a] -> [a]
deleteNth n (x : xs)
    | n == 0 = xs
    | n > 0 = x : deleteNth (n - 1) xs
deleteNth n _
    | n < 0 = error "Utilities.deleteNth: negative index"
    | otherwise = error "Utilities.deleteNth: index too large"

-- Replace the nth item in a list
replaceNth :: a -> Int -> [a] -> [a]
replaceNth z n (x : xs)
    | n == 0 = z : xs
    | n > 0 = x : replaceNth z (n - 1) xs
replaceNth _ n _
    | n < 0 = error "Utilities.replaceNth: negative index"
    | otherwise = error "Utilities.replaceNth: negative index"

maybeNth :: [a] -> Int -> Maybe a
maybeNth as i =
    case i < L.length as of
      True -> Just (as !! i)
      False -> Nothing

listMax :: Ord a => [a] -> Maybe a
listMax [] = Nothing
listMax [a] = Just a
listMax (a : rest) =
    do
      maxRest <- listMax rest
      Just $ max a maxRest

-- given a function of two args and two lists, return the list of
-- results of applying the function to the successive members.
--
-- If one list is longer, discard its excess members.

mapTwo :: (a -> b -> c) -> [a] -> [b] -> [c]
mapTwo f as bs =
    map (\(a,b) -> f a b) (zip as bs)

foldrTwo :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldrTwo f seed as bs =
    foldr (\(a,b) c -> f a b c) seed (zip as bs)

-- Returns a list of the natural numbers less that the argument.
{-# INLINE nats #-}
nats :: Int -> [Int]
nats n = [0..(n - 1)]

{-# INLINE assert #-}
assert :: MonadFail m => (a -> Bool) -> a -> m a
assert pred x
    | pred x = return x
    | otherwise = fail "assertion failed"

assertError :: [Char] -> a
assertError s = error ("[ASSERT FAILED] " ++ s)

seqList :: [a] -> [a]
seqList xs =
    loop xs
    where
      loop [] = xs
      loop (y : ys) = seq y (loop ys)

-- Is graph acyclic?
isAcyclic :: Ord a => (a -> [a]) -> [a] -> Bool
isAcyclic adj nodes =
    all (not . backEdge numbering) edges
    where
      numbering = dfs adj start
      -- Remove nodes that have non-zero indegree
      start = foldl' (flip L.delete) nodes (map fst edges)
      edges = [ (dst, src) | src <- nodes, dst <- adj src ]

-- Compute a depth first search numbering of nodes using postorder.
-- With postorder, only back edges go from a lower number to a higher
-- one.  Assumes nodes, the set of nodes with indegree zero, is not empty.
dfs :: Ord a => (a -> [a]) -> [a] -> [(a, Int)]
dfs adj nodes =
    alist
    where
      (_, alist, _) = foldl' po (0, [], S.empty) nodes
      po a@(num, alist, seen) node
         | S.member node seen = a
         | otherwise =
             (num' + 1, (node, num') : alist', seen'')
             where  -- Search is postorder because nodes at the end of
               (num', alist', seen'') = -- edges are explored before
                   foldl' po (num, alist, seen') nodes' -- the node
               seen' = S.insert node seen -- Insert node as soon as
               nodes' = adj node          -- it's seen

-- Is edge a back edge, meaning a cycle has been found?  If an edge
-- contains a node that is not in the alist, it means it was not
-- visited during the depth first seach.  This can happen when there
-- is a strong component that has no edges from other strong
-- components to it.  We report this edge to be a back edge so as to
-- get the correct overall result.
backEdge :: Eq a => [(a, Int)] -> (a, a) -> Bool
backEdge alist (node, node') =
    case (lookup node alist, lookup node' alist) of
      (Just n, Just n') -> n >= n'
      _ -> True
