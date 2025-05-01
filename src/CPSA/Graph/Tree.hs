-- Generate an SVG drawing of a tree of preskeletons

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Graph.Tree (Tree (..), Forest, forest, tree) where

--import System.IO.Unsafe
import qualified Data.Map as M
import Data.Map (Map)
import Data.List (foldl')
--import Data.List (elem)
import qualified Data.Set as S
import Data.Set (Set)
--import Data.Maybe (mapMaybe)
import CPSA.Lib.Utilities (seqList)
import CPSA.Graph.XMLOutput
import CPSA.Graph.Config
import CPSA.Graph.SVG
import CPSA.Graph.Loader

-- The preskeletons in the output are assembled together for display
-- into trees based on the parent relation.  In reality, the
-- relationship between preskeletons is not tree-like, but includes
-- other edges as a result of a preskeleton having cohort members that
-- have been seen before.  These members are called a tree node's
-- duplicates, and their children are displayed somewhere else in the
-- display.
{- 
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x -}

data Tree = Tree
    { vertex :: !Preskel,
      children :: !Forest,      -- Freshly discovered preskeletons
      duplicates :: !Forest,    -- Preskeletons already seen
      alive :: !Bool,           -- Is preskeleton alive?
      width :: !Int,            -- Number of leaf nodes
      height :: !Int }          -- Longest distance to a leaf plus one
    deriving Show

instance Eq Tree where
    t0 == t1 = vertex t0 == vertex t1

instance Ord Tree where
    compare t0 t1 = compare (vertex t0) (vertex t1)

makeTree :: Preskel -> [Tree] -> [Tree] -> Tree
makeTree k kids dups =
    Tree { vertex = k,
           children = seqList kids,
           duplicates = seqList dups,
           alive = True, -- This will be repaired later
           width = x kids dups,
           height = y kids dups }
    where
      x [] [] = 1
      -- The width of a duplicate is one
      x kids dups = sum (map width kids) + length dups
      -- The height of a duplicate is one
      y kids dups = 1 + foldl max (dupsHeight dups) (map height kids)
      dupsHeight [] = 0
      dupsHeight _ = 1

type Forest = [Tree]

-- Assemble preskeletons into a forest and then set the alive flag
forest :: [Preskel] -> Forest
forest ks =
    map setLiveness (reverse (foldl' f [] ks))
    where
      f ts k
        | parent k == Nothing = -- Found tree root
            assemble (childMap ks) k : ts
        | otherwise = ts        -- Otherwise skip k

-- A child map maps a label to a preskeleton and a list of its
-- childnen.  The map is derived by looking at the parent field.  The
-- code assumes a parent precedes its children in the input list.
childMap :: [Preskel] -> Map Int (Preskel, [Preskel])
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
assemble :: Map Int (Preskel, [Preskel]) -> Preskel -> Tree
assemble table k =
    makeTree k (kids k) (dups k)
    where
      kids k =
          case M.lookup (label k) table of
            Nothing -> []       -- This should never happen
            Just (_, ks) -> map (assemble table) (reverse ks)
      dups k =
          [ makeTree k' [] []   -- Make an empty tree for a duplicate
            | tag <- seen k,
              k' <- maybe [] (\(k, _) -> [k]) (M.lookup tag table) ]

-- Set the alive flag in each preskeleton.
setLiveness :: Tree -> Tree
setLiveness t =
    updateLiveness (live (vertexMap t) t) t

-- Make a map of all the vertices in a tree 
vertexMap :: Tree -> Map Int Tree
vertexMap t =
    loop t $ M.insert (label $ vertex t) t M.empty
    where
        loop t m =
            foldl (\m' t' -> loop t' $ M.insert (label $ vertex t') t' m')
                  m (children t)

-- Extract all preskeletons from a tree.
preskeletons :: Tree -> Set Preskel
preskeletons t =  let ks = foldl' S.union S.empty $ map preskeletons (children t) in
    S.insert (vertex t) ks

-- Extract all the subtrees from a tree.
{- trees :: Tree -> Set Tree
trees t = let ks = foldl' S.union S.empty $ map trees (children t) in 
    S.insert t ks -}

-- Extract the non-dead preskeletons from a tree.  
{- live :: Map Int Tree -> Tree -> Set Preskel
live vmap t = loop liveLeaves
    where
        preskels = preskeletons t
        liveLeaf :: Preskel -> Bool
        liveLeaf k = shape k || aborted k || (not (realized k) && not (dead k))
        liveLeaves = S.filter liveLeaf preskels

        getTree :: Preskel -> Maybe Tree
        getTree = (`M.lookup` vmap) . label

        allKids :: Preskel -> Set Preskel
        allKids k = S.fromList (map vertex (
                maybe [] children (getTree k) ++
                mapMaybe (getTree . vertex) (maybe [] duplicates (getTree k))
            ))

        loop :: Set Preskel -> Set Preskel
        loop old = let new = ascend old in
            if S.size new == S.size old then
                old
            else
                loop new
        ascend :: Set Preskel -> Set Preskel
        -- add all of the preskeletons whose set of children
        -- is not disjoint from the preskels currently marked live
        ascend old = S.union (S.filter (not . S.disjoint old . allKids) preskels) old -}

    

live :: Map Int Tree -> Tree -> Set Preskel
live vmap t = loop liveLeaves
    where
        preskels = preskeletons t
        
        -- Aborting and/or ctrl+c might leave a live fringe. 
        -- The cases below check for those conditions.
        getLiveLeaves :: [Int] -> Set Preskel -> Tree -> Set Preskel 
        getLiveLeaves as ps t = 
            let k = vertex t 
                l = label k in 
                -- aborted skeletons are live fringe and have no children
                if aborted k then 
                    S.insert k ps 
                -- shapes are always live but may have children
                else if shape k then 
                    S.insert k (foldl (getLiveLeaves (l:as)) ps (children t))
                -- if it can't be made into a skeleton, it's not a live leaf
                else if noSkel k then 
                    ps
                -- if rules apply but it has no children, it dies on 
                -- rule application. Not a live leaf.
                else if children t == [] && rulesApply k then 
                    ps
                -- realized skeletons that aren't shapes
                -- but have no children are live fringe
                else if children t == [] && realized k then 
                    S.insert k ps 
                -- If it has no children or seen children, isn't realized or dead
                -- it's live fringe
                else if children t == [] && duplicates t == [] &&
                    not (realized k) && not (dead k) then 
                    S.insert k ps
                -- If it only has seen children, and they are all 
                -- ancestors, it's not a live leaf
                else if children t == [] && not (realized k) && 
                    not (dead k) && duplicates t /= [] &&
                    isSubList (map (label . vertex) $ duplicates t) as then 
                        ps
                -- otherwise it's not a live leaf. Descend without adding
                else 
                    foldl (getLiveLeaves (l:as)) ps (children t)

        isSubList :: Eq a => [a] -> [a] -> Bool
        isSubList [] _ = True
        isSubList _ [] = False
        isSubList (x:xs) ys = elem x ys && isSubList xs ys

        liveLeaves = getLiveLeaves [] S.empty t

        getTree :: Preskel -> Tree
        getTree k =
            case (`M.lookup` vmap) $ label k of
                -- Will only be used on skeletons in the vmap
                Nothing -> error $ "getTree': Preskel not found: " ++ show k
                Just t -> t

        allKids :: Preskel -> Set Preskel
        allKids k = S.fromList (map vertex (
                children (getTree k) ++
                map (getTree . vertex) (duplicates (getTree k))
            ))

        loop :: Set Preskel -> Set Preskel
        loop old = let new = ascend old in
            if S.size new == S.size old then
                old
            else
                loop new
        ascend :: Set Preskel -> Set Preskel
        -- add all of the preskeletons whose set of children
        -- is not disjoint from the preskels currently marked live
        ascend old = S.union (S.filter (not . S.disjoint old . allKids) preskels) old


updateLiveness :: Set Preskel -> Tree -> Tree
updateLiveness live t =
    t { children = map (updateLiveness live) (children t),
        duplicates = map (updateLiveness live) (duplicates t),
        alive = S.member (vertex t) live }

-- Draw tree view of preskeleton relations
tree :: Config -> Tree -> (Float, Float, [Element])
tree conf t =
    if compact conf then
        vtree conf t
    else
        htree conf t

-- Draw a vertical tree
vtree :: Config -> Tree -> (Float, Float, [Element])
vtree conf t =
    (w, h, snd $ folddup (loop x y) (mx conf, top) t)
    where
      tw = tx conf * fromIntegral (width t - 1)  -- Tree width
      th = ty conf * fromIntegral (height t - 1) -- Tree height
      x = mx conf + tw / 2
      y = my conf
      top = [button conf x y False t]
      loop :: Float -> Float -> Bool -> (Float, [Element]) ->
              Tree -> (Float, [Element])
      loop x1 y1 dup (w, es) t =
          (w + tx conf + tw, es')
          where
            x2 = w + tw / 2
            y2 = y1 + ty conf
            es'' = button conf x2 y2 dup t :
                   line conf x1 (y1 + td conf) x2 (y2 - ta conf) : es
            es' = snd $ folddup (loop x2 y2) (w, es'') t
            tw = tx conf * fromIntegral (width t - 1)
      w = 2 * mx conf + tw                       -- Diagram width
      h = 2 * my conf + th                       -- Diagram height

-- Draw a horizontal tree
htree :: Config -> Tree -> (Float, Float, [Element])
htree conf t =
    (w, h, snd $ folddup (loop x y) (my conf, top) t)
    where
      tw = tx conf * fromIntegral (height t - 1)  -- Tree width
      th = ty conf * fromIntegral (width t - 1)   -- Tree height
      x = mx conf
      y = my conf + th / 2
      top = [button conf x (y - td conf) False t]
      loop :: Float -> Float -> Bool -> (Float, [Element]) ->
              Tree -> (Float, [Element])
      loop x1 y1 dup (h, es) t =
          (h + ty conf + th, es')
          where
            x2 = x1 + tx conf
            y2 = h + th / 2
            es'' = button conf x2 (y2 - td conf) dup t :
                   line conf x1 y1 x2 y2 : es
            es' = snd $ folddup (loop x2 y2) (h, es'') t
            th = ty conf * fromIntegral (width t - 1)
      w = 2 * mx conf + tw                       -- Diagram width
      h = 2 * my conf + th                       -- Diagram height

folddup :: (Bool -> a -> Tree -> a) -> a -> Tree -> a
folddup f z t =
    foldl (f False) (foldl (f True) z (duplicates t)) (children t)

button :: Config -> Float -> Float -> Bool -> Tree -> Element
button conf x y dup t =
    kbutton conf x y kind (label (vertex t))
    where
      kind =
          case (alive t, dup) of
            (True, False) ->
                if shape (vertex t) then Shape
                else if realized (vertex t) then Realized
                     else AliveTree
            (True, True) -> AliveDup
            (False, False) -> DeadTree
            (False, True) -> DeadDup
