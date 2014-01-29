-- Term reduction for the CPSA solver.

-- Copyright (c) 2010 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

-- Provides the top-level search loop, which implements term reduction
-- on skeletos.

module CPSA.Lib.Reduction (solve) where

import System.IO
import Control.Parallel
import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Lib.Algebra
import CPSA.Lib.Strand
import CPSA.Lib.Cohort
import CPSA.Lib.Displayer

-- Set when debugging an exception so that buffered results get out.
useFlush :: Bool
useFlush = False                -- True

-- Parameter driven S-expression printer
wrt :: Options -> Handle -> SExpr a -> IO ()
wrt p h sexpr =
    do
      writeLnSEexpr h (optMargin p) sexpr
      if useFlush then hFlush h else return ()

-- A labeled and linked preskeleton
data LPreskel t g s e
    = LPreskel { content :: Preskel t g s e,
                 label :: Int,
                 parent :: Maybe (LPreskel t g s e) }
      deriving Show

-- A skeleton that has been seen before need not be reanalyzed.
-- Instead, one looks up the label of the skeleton seen before, and
-- returns it.  What follows is the data structure used to store
-- information in the seen history used for the isomorphism check.
-- The integer is the label of the seen skeleton.
type IPreskel t g s e = (Gist t g, Int)

-- Is the skeleton summarized by gist g isomorphic to one with the
-- given label?
wasSeen :: Algebra t p g s e c => Gist t g ->
           IPreskel t g s e -> Bool
wasSeen g (g', _) = isomorphic g g'

-- A seen history as a list.

newtype Seen t g s e = Seen [IPreskel t g s e]

-- Create a singleton seen history
hist :: Algebra t p g s e c => IPreskel t g s e -> Seen t g s e
hist ik = Seen [ik]

-- Add an element to the seen history.
remember :: Algebra t p g s e c => IPreskel t g s e ->
            Seen t g s e -> Seen t g s e
remember ik (Seen seen) = Seen (ik : seen)

-- Find an element of the seen history that satisfies a predicate.
recall :: Algebra t p g s e c => (IPreskel t g s e -> Bool) ->
          Seen t g s e -> Maybe (IPreskel t g s e)
recall f (Seen seen) = L.find f seen

-- Create an empty seen history
void :: Algebra t p g s e c => Seen t g s e
void = Seen []

-- Merge two seen histories.
merge :: Algebra t p g s e c => Seen t g s e ->
         Seen t g s e -> Seen t g s e
merge (Seen xs) (Seen ys) = Seen (xs ++ ys)

-- Contains the result of applying the cohort reduction rule.  The
-- last position is used to hold the reverse of the labels of the
-- seen children
data Reduct t g s e  =
    Reduct !(LPreskel t g s e) !Int !Bool ![Preskel t g s e] ![Int]

parMap :: (a -> b) -> [a] -> [b]
parMap _ [] = []
parMap f (x:xs) =
    par y (pseq ys (y:ys))
    where
      y = f x
      ys = parMap f xs

{--  Turn off parallism with this:

parMap :: (a -> b) -> [a] -> [b]
parMap = map

-}

-- Entry point for analysis
solve :: Algebra t p g s e c => Options -> Handle ->
         [Preskel t g s e] -> Int -> IO ()
solve _ h [] _ =                -- Done
    hClose h
solve p h (k : ks) n =
    do
      wrt p h (displayProt (protocol k)) -- show protocol
      case firstSkeleton k of
        [] ->                  -- Input cannot be made into a skeleton
            do
              let lk = LPreskel k n Nothing
              wrt p h (commentPreskel lk [] (unrealized k) False
                       "Input cannot be made into a skeleton--nothing to do")
              solve p h ks (n + 1)
        [k'] ->
            if isomorphic (gist k) (gist k') then -- Input was a skeleton
                let lk' = LPreskel k' n Nothing in
                begin p h ks (n + optLimit p) (n + 1)
                         (hist (gist k', n)) [lk']
            else                -- Input was not a skeleton
                do
                  let lk = LPreskel k n Nothing
                  wrt p h (commentPreskel lk [] (unrealized k) False
                           "Not a skeleton")
                  let lk' = LPreskel k' (n + 1) (Just lk)
                  begin p h ks (n + optLimit p) (n + 2)
                           (hist (gist k', n + 1))  [lk']
        _ -> error "Main.solve: can't handle more than one skeleton"

-- Begin by collapsing the point-of-view skeleton as much as possible.
begin :: Algebra t p g s e c => Options -> Handle ->
         [Preskel t g s e] -> Int -> Int -> Seen t g s e ->
         [LPreskel t g s e] -> IO ()
begin p h ks m n seen todo =
    search p h ks m n seen todo []

-- Apply collapse until all possibilities are exhausted.
search :: Algebra t p g s e c => Options -> Handle ->
            [Preskel t g s e] -> Int -> Int -> Seen t g s e ->
            [LPreskel t g s e] -> [LPreskel t g s e] -> IO ()
search p h ks m n seen [] done =
    mode p h ks m n seen (reverse done)
search p h ks m n seen (lk:todo) done =
    do
      let kids = collapse (content lk)
      let (n', seen', todo', _) =
              foldl (next lk) (n, seen, todo, []) kids
      search p h ks m n' seen' todo' (lk:done)

-- Select reduction mode, noIsoChk or normal
mode :: Algebra t p g s e c => Options -> Handle ->
        [Preskel t g s e] -> Int -> Int -> Seen t g s e ->
        [LPreskel t g s e] -> IO ()
mode p h ks m n seen todo =
    if optNoIsoChk p then
        fast p h ks m n todo     -- Peform no isomorphism checks
    else
        breadth p h ks m n seen todo []

-- The main loop is implemented using breadth and step.  Tail calls
-- are used to ensure they do not add to the control stack.

-- Function breadth handles one level of the derivation tree.
-- This ensures a breadth first derivation order.
--
-- p is the runtime options
-- h is the output handle
-- ks is the list of problems
-- m is the step limit
-- n is the current step count
-- seen holds the gists of seen skeletons
-- todo holds unreduced skeletons
-- tobig holds skeletons that have exceed the strand bound.
breadth :: Algebra t p g s e c => Options -> Handle ->
           [Preskel t g s e] -> Int -> Int -> Seen t g s e ->
           [LPreskel t g s e] -> [LPreskel t g s e] -> IO ()
breadth p h ks _ n _ [] [] =       -- Empty todo list and tobig list
    do
      wrt p h (comment "Nothing left to do")
      solve p h ks n            -- Solve next problem
breadth p h _ _ _ _ [] tobig = -- Empty todo list and non-null tobig list
    do
      wrt p h (comment "Strand bound exceeded--aborting run")
      dump p h (reverse tobig)  "Strand bound exceeded"
breadth p h ks m n seen todo tobig =
    step p h ks m seen n void [] tobig (parMap (branch p seen) todo)

-- Function step handles one skeleton in one level of the tree.
step :: Algebra t p g s e c => Options -> Handle ->
        [Preskel t g s e] -> Int -> Seen t g s e -> Int ->
        Seen t g s e -> [LPreskel t g s e] ->
        [LPreskel t g s e] -> [Reduct t g s e] -> IO ()
step p h ks m oseen n seen todo tobig [] = -- Empty reducts
    breadth p h ks m n (merge seen oseen) (reverse todo) tobig
step p h _ m _ n _ todo tobig reducts
    | n > m =                   -- Check step count
        do
          wrt p h (comment "Step limit exceeded--aborting run")
          dump p h (mktodo reducts todo tobig) "Step limit exceeded"
step p h ks m oseen n seen todo tobig (Reduct lk _ _  _  _ : reducts)
    | nstrands (content lk) >= optBound p = -- Check strand count
        step p h ks m oseen n seen todo (lk : tobig) reducts
step p h ks m oseen n seen todo tobig (Reduct lk size cols kids dups : reducts)
    | size <= 0 =               -- Interpret empty reducts
        do
          let ns = unrealized (content lk)
          let shape = null ns
          wrt p h  (commentPreskel lk [] ns shape
                    (if shape then "" else "empty cohort"))
          step p h ks m oseen n seen todo tobig reducts
    | otherwise =
        do
          let (n', seen', todo', dups') =
                  foldl (next lk) (n, seen, todo, dups) kids
          let ns = unrealized (content lk)
          let u = size - length dups'
          let msg = shows size $ showString " in cohort - " $
                         shows u " not yet seen"
          wrt p h  (commentPreskel lk (reverse dups') ns cols msg)
          step p h ks m oseen n' seen' todo' tobig reducts

-- Expands one branch in the derivation tree.
branch :: Algebra t p g s e c => Options -> Seen t g s e ->
          LPreskel t g s e -> Reduct t g s e
branch p seen lk =
    Reduct lk (length kids) cols
               (seqList $ reverse unseen) (seqList dups)
    where
      kids = reduce (mkMode p) (content lk)
      cols = all collapsed kids
      (unseen, dups) =
          foldl (duplicates seen) ([], []) kids

mkMode :: Options -> Mode
mkMode p =
    Mode { noGeneralization = optNoIsoChk p,
           nonceFirstOrder = optCheckNoncesFirst p,
           visitOldStrandsFirst = optTryOldStrandsFirst p,
           reverseNodeOrder = optTryYoungNodesFirst p}

-- Is preskeleton the result of a collapsing operation?
collapsed :: Algebra t p g s e c => Preskel t g s e -> Bool
collapsed k =
    case operation k of
      Collapsed _ _ -> True
      _ -> False

duplicates :: Algebra t p g s e c => Seen t g s e ->
              ([Preskel t g s e], [Int]) ->
                  Preskel t g s e -> ([Preskel t g s e], [Int])
duplicates seen (unseen, dups) kid =
    case recall (wasSeen $ gist kid) seen of
      Just (_, label) -> (unseen, label : dups)
      Nothing -> (kid : unseen, dups)

-- Make a todo list for dump
mktodo :: Algebra t p g s e c => [Reduct t g s e] ->
          [LPreskel t g s e] -> [LPreskel t g s e] ->
          [LPreskel t g s e]
mktodo reducts todo tobig =
    map (\(Reduct lk _ _ _ _) -> lk) reducts ++ reverse todo ++ reverse tobig

type Next t p g s e c =
    (Int, Seen t g s e, [LPreskel t g s e], [Int])

-- Update state variables used by step.
next :: Algebra t p g s e c => LPreskel t g s e ->
        Next t p g s e c -> Preskel t g s e ->
        Next t p g s e c
next p (n, seen, todo, dups) k =
    let g = gist k in
    case recall (wasSeen g) seen of
      Just (_, label) ->
          (n, seen, todo, label : dups)
      Nothing ->
          (n + 1, remember (g, n) seen, lk : todo, dups)
          where
            lk = LPreskel k n (Just p) -- Label a preskeleton here

-- This function reduces without checking for isomorphisms
fast :: Algebra t p g s e c => Options -> Handle ->
        [Preskel t g s e] -> Int -> Int ->
        [LPreskel t g s e] -> IO ()
fast p h ks _ n [] =            -- Empty todo list
    do
      wrt p h (comment "Nothing left to do")
      solve p h ks n
fast p h _ m n todo
    | n > m =                   -- Check step count
        do
          wrt p h (comment "Step limit exceeded--aborting run")
          dump p h todo "Step limit exceeded"
fast p h _ _ _ todo@(lk : _)
    | nstrands (content lk) >= optBound p = -- Check strand count
        do
          wrt p h (comment "Strand bound exceeded--aborting run")
          dump p h todo "Strand bound exceeded"
fast p h ks m n (lk : todo) =
    do
      let ns = unrealized (content lk)
      let ks' = reduce (mkMode p) (content lk)
      let msg = show (length ks') ++ " in cohort"
      wrt p h (commentPreskel lk [] ns (null ns) msg)
      let (n', todo') = foldl (children lk) (n, []) ks'
      fast p h ks m n' (todo ++ reverse todo')

children :: Algebra t p g s e c => LPreskel t g s e ->
            (Int, [LPreskel t g s e]) ->
            Preskel t g s e -> (Int, [LPreskel t g s e])
children p (n, todo) k =        -- Label a preskeleton here
    (n + 1, LPreskel k n (Just p) : todo)

-- Print partial results in a form that works with analysis tools
dump :: Algebra t p g s e c => Options -> Handle ->
        [LPreskel t g s e] -> String -> IO ()
dump _ h [] msg =
    do
      hClose h
      abort msg
dump p h (lk : lks) msg =
    do
      let ns = unrealized $ content lk
      wrt p h (commentPreskel lk [] ns False "aborted")
      dump p h lks msg

-- Add a label, maybe a parent, a list of seen preskeletons isomorphic
-- to some members of this skeleton's cohort, and a list of unrealized
-- nodes.  If it's a shape, note this fact.  Add a comment if present.
commentPreskel :: Algebra t p g s e c => LPreskel t g s e ->
                  [Int] -> [Node] -> Bool -> String -> SExpr ()
commentPreskel lk seen unrealized shape msg =
    displayPreskel k $
    addKeyValues "label" [N () (label lk)] $
    maybeAddVKeyValues "parent" (\p -> [N () (label p)]) (parent lk) $
    condAddKeyValues "seen" (not $ null seen)
                     (map (N ()) (L.sort (L.nub seen))) $
    addKeyValues "unrealized" (map displayNode $ L.sort unrealized) $
    condAddKeyValues "shape" shape [] $
    -- Structure preserving maps
    -- Added for cpsalogic program
    condAddKeyValues "maps" shape (maps k) $
    -- Nodes of origination
    -- Added for cpsalogic program
    condAddKeyValues "origs" (starter k || shape) (origs k) $
    -- Messages
    case msg of
      "" -> []
      -- Preskeleton key added for cpsalogic program
      "Not a skeleton" -> addKeyValues "preskeleton" [] [comment msg]
      _ -> [comment msg]
    where
      k = content lk
      starter k =               -- True for the POV skeleton and
          case pov k of         -- just a few others
            Nothing -> False
            Just k' -> nstrands k == nstrands k'

addKeyValues :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]
addKeyValues key values rest =
    L () (S () key : values) : rest

condAddKeyValues :: String -> Bool -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]
condAddKeyValues _ False _ rest =
    rest
condAddKeyValues key True values rest =
    addKeyValues key values rest

maybeAddVKeyValues :: String -> (a -> [SExpr ()]) -> Maybe a ->
                      [SExpr ()] -> [SExpr ()]
maybeAddVKeyValues _ _ Nothing rest =
    rest
maybeAddVKeyValues key f (Just x) rest =
    addKeyValues key (f x) rest

-- Prints structure preserving maps (homomorphisms)
maps :: Algebra t p g s e c => Preskel t g s e -> [SExpr ()]
maps k =
    map (amap $ strandMap k) (envMaps k)
    where
      amap strands env = L () [L () strands, L () env]
      strandMap k = map (N ()) (prob k)
      envMaps k =
          case pov k of
            Nothing -> []
            Just k' ->
                map (displayEnv (ctx k') (ctx k)) (homomorphism k' k (prob k))
      ctx k = addToContext emptyContext (kvars k)

-- Prints the nodes of origination for each uniquely originating atom
origs :: Algebra t p g s e c => Preskel t g s e -> [SExpr ()]
origs k =
    [ L () [displayTerm ctx t, displayNode n]
      | (t, ns) <- korig k, n <- ns ]
    where
      ctx = addToContext emptyContext (kvars k)
