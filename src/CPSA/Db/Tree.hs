-- Generate a tree of preskeletons

-- This code is based on what is in CPSA.Graph.Tree

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Db.Tree (Tree (..), Forest, forest) where

import qualified Data.Map as M
import Data.Map (Map)
import Data.List (foldl')
import CPSA.Lib.Utilities (seqList)
import CPSA.Db.Structs

-- The preskeletons in the output are assembled together for display
-- into trees based on the parent relation.  In reality, the
-- relationship between preskeletons is not tree-like, but includes
-- other edges as a result of a preskeleton having cohort members that
-- have been seen before.  These members are called a tree node's
-- duplicates, and their children are displayed somewhere else in the
-- display.

data Tree = Tree
    { vertex :: !Skel,
      children :: !Forest,      -- Freshly discovered preskeletons
      duplicates :: !Forest }   -- Preskeletons already seen
    deriving Show

makeTree :: Skel -> [Tree] -> [Tree] -> Tree
makeTree k kids dups =
    Tree { vertex = k,
           children = seqList kids,
           duplicates = seqList dups }

type Forest = [Tree]

-- Assemble preskeletons into a forest and then set the alive flag
forest :: [Skel] -> Forest
forest ks =
    reverse (foldl' f [] ks)
    where
      f ts k
        | parent k == Nothing = -- Found tree root
            assemble (childMap ks) k : ts
        | otherwise = ts        -- Otherwise skip k

-- A child map maps a label to a preskeleton and a list of its
-- childnen.  The map is derived by looking at the parent field.  The
-- code assumes a parent precedes its children in the input list.
childMap :: [Skel] -> Map Int (Skel, [Skel])
childMap ks =
    foldl' child M.empty ks
    where
      child cm k =
          case parent k of
            Nothing -> cm'
            Just p ->
                M.adjust addChild p cm'
          where
            cm' = M.insert (label k) (k, []) cm
            addChild (k', children) =
                (k', k : children)

-- Assemble preskeletons into a tree
assemble :: Map Int (Skel, [Skel]) -> Skel -> Tree
assemble table k =
    makeTree k (kids k) (dups k)
    where
      kids k =
          case M.lookup (label k) table of
            Nothing -> []       -- This should never happen
            Just (_, ks) -> map (assemble table) (reverse ks)
      dups k =
          [ makeTree k' [] []   -- Make an empty tree for a duplicate
            | (tag, _) <- seen k,
              k' <- maybe [] (\(k, _) -> [k]) (M.lookup tag table) ]
