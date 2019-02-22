-- Term reduction for the CPSA solver.

-- Copyright (c) 2010 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

-- Provides the top-level search loop, which implements term reduction
-- on skeletos.

module CPSA.Reduction (solve) where

import System.IO
import Control.Parallel
import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Options
import CPSA.Algebra
import CPSA.Protocol
import CPSA.Strand
import CPSA.Cohort
import CPSA.Displayer

-- Set when debugging an exception so that buffered results get out.
useFlush :: Bool
useFlush = False                -- True

-- Parameter driven S-expression printer
wrt :: Options -> Handle -> SExpr a -> IO ()
wrt p h sexpr =
    do
      writeLnSExpr h (optMargin p) sexpr
      if useFlush then hFlush h else return ()

-- A labeled and linked preskeleton
data LPreskel
    = LPreskel { content :: Preskel,
                 label :: Int,
                 depth :: Int,
                 parent :: Maybe LPreskel }
      deriving Show

withParent :: Preskel -> Int ->  LPreskel -> LPreskel
withParent k label parent =
    LPreskel k label (1 + depth parent) (Just parent)

-- A skeleton that has been seen before need not be reanalyzed.
-- Instead, one looks up the label of the skeleton seen before, and
-- returns it.  What follows is the data structure used to store
-- information in the seen history used for the isomorphism check.
-- The integer is the label of the seen skeleton.
type IPreskel = (Gist, Int)

-- Is the skeleton summarized by gist g isomorphic to one with the
-- given label?
wasSeen :: Gist -> IPreskel -> Bool
wasSeen g (g', _) = isomorphic g g'

-- A seen history as a list.

newtype Seen = Seen [IPreskel]

-- Create a singleton seen history
hist :: IPreskel -> Seen
hist ik = Seen [ik]

-- Add an element to the seen history.
remember :: IPreskel -> Seen -> Seen
remember ik (Seen seen) = Seen (ik : seen)

-- Find an element of the seen history that satisfies a predicate.
recall :: (IPreskel -> Bool) -> Seen -> Maybe (IPreskel)
recall f (Seen seen) = L.find f seen

-- Create an empty seen history
void :: Seen
void = Seen []

-- Merge two seen histories.
merge :: Seen -> Seen -> Seen
merge (Seen xs) (Seen ys) = Seen (xs ++ ys)

-- Contains the result of applying the cohort reduction rule.  The
-- last position is used to hold the reverse of the labels of the
-- seen children
data Reduct t g s e  =
    Reduct !(LPreskel) !Int ![Preskel] ![Int]

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
-- n is the step count
solve :: Options -> Handle -> [Preskel] -> Int -> IO ()
solve _ h [] _ =                -- Done
    hClose h
solve p h (k : ks) n =
    do
      wrt p h (displayProt (protocol k)) -- show protocol
      case firstSkeleton k of
        [] ->                  -- Input cannot be made into a skeleton
            do
              let lk = LPreskel k n 0 Nothing
              wrt p h (commentPreskel lk [] (unrealized k) Ordinary Nada
                       "Input cannot be made into a skeleton--nothing to do")
              solve p h ks (n + 1)
        [k'] ->
            if isomorphic (gist k) (gist k') then -- Input was a skeleton
                let lk' = LPreskel k' n 0 Nothing in
                begin p h ks (n + optLimit p) (n + 1)
                         (hist (gist k', n)) lk'
            else                -- Input was not a skeleton
                do
                  let lk = LPreskel k n (-1) Nothing
                  wrt p h (commentPreskel lk [] (unrealized k) Ordinary
                           Preskeleton "Not a skeleton")
                  let lk' = withParent k' (n + 1) lk
                  begin p h ks (n + optLimit p) (n + 2)
                           (hist (gist k', n + 1)) lk'
        _ -> error "Main.solve: can't handle more than one skeleton"

-- Begin by applying rules as much as possible.
begin :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
         LPreskel -> IO ()
begin p h ks m n seen lk =
  let k = content lk in
  case rewrite k of
    Nothing -> search p h ks m n seen [lk] []
    Just kids ->
      do
        wrt p h (commentPreskel lk [] (unrealized k) Ordinary
                  Nada "Not closed under rules")
        let (n', seen', todo', _) =
              foldl (next lk) (n, seen, [], []) kids
        search p h ks m n' seen' todo' []

-- Apply collapse until all possibilities are exhausted.
search :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
            [LPreskel] -> [LPreskel] -> IO ()
search p h ks m n seen [] done =
    mode p h ks m n seen (reverse done)
search p h ks m n seen (lk:todo) done =
    do
      let kids = concatMap simplify (collapse $ content lk)
      let (n', seen', todo', _) =
              foldl (next lk) (n, seen, todo, []) kids
      search p h ks m n' seen' todo' (lk:done)

-- Select reduction mode, noIsoChk or normal
mode :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
        [LPreskel] -> IO ()
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
breadth :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
           [LPreskel] -> [LPreskel] -> IO ()
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
step :: Options -> Handle -> [Preskel] -> Int -> Seen -> Int ->
        Seen -> [LPreskel] -> [LPreskel] -> [Reduct t g s e] -> IO ()
step p h ks m oseen n seen todo tobig [] = -- Empty reducts
    breadth p h ks m n (merge seen oseen) (reverse todo) tobig
step p h _ m _ n _ todo tobig reducts
    | n > m =                   -- Check step count
        do
          wrt p h (comment "Step limit exceeded--aborting run")
          dump p h (mktodo reducts todo tobig) "Step limit exceeded"
step p h ks m oseen n seen todo tobig (Reduct lk _ _  _  : reducts)
    | nstrands (content lk) >= optBound p = -- Check strand count
        step p h ks m oseen n seen todo (lk : tobig) reducts
step p h ks m oseen n seen todo tobig (Reduct lk size kids dups : reducts)
    | size <= 0 =               -- Interpret empty reducts
        do
          let ns = unrealized (content lk)
          let shape = null ns
          case shape of
            True -> wrt p h (commentPreskel lk [] ns Shape Nada "")
            False ->
              wrt p h (commentPreskel lk [] ns Ordinary Dead "empty cohort")
          step p h ks m oseen n seen todo tobig reducts
    | optDepth p > 0 && depth lk >= optDepth p =
        do
          let ns = unrealized (content lk)
          wrt p h (commentPreskel lk [] ns Fringe Nada "")
          step p h ks m oseen n seen todo tobig reducts
    | otherwise =
        do
          let (n', seen', todo', dups') =
                  foldl (next lk) (n, seen, todo, dups) kids
          let ns = unrealized (content lk)
          let u = size - length dups'
          let msg = shows size $ showString " in cohort - " $
                         shows u " not yet seen"
          wrt p h (commentPreskel lk (reverse dups') ns Ordinary Nada msg)
          step p h ks m oseen n' seen' todo' tobig reducts

-- Expands one branch in the derivation tree.
branch :: Options -> Seen -> LPreskel -> Reduct t g s e
branch p seen lk =
    Reduct lk (length kids)
               (seqList $ reverse unseen) (seqList dups)
    where
      kids = reduce (mkMode p) (content lk)
      (unseen, dups) =
          foldl (duplicates seen) ([], []) kids

mkMode :: Options -> Mode
mkMode p =
    Mode { noGeneralization = optNoIsoChk p,
           nonceFirstOrder = optCheckNoncesFirst p,
           visitOldStrandsFirst = optTryOldStrandsFirst p,
           reverseNodeOrder = optTryYoungNodesFirst p}

duplicates :: Seen -> ([Preskel], [Int]) -> Preskel -> ([Preskel], [Int])
duplicates seen (unseen, dups) kid =
    case recall (wasSeen $ gist kid) seen of
      Just (_, label) -> (unseen, label : dups)
      Nothing -> (kid : unseen, dups)

-- Make a todo list for dump
mktodo :: [Reduct t g s e] -> [LPreskel] -> [LPreskel] -> [LPreskel]
mktodo reducts todo tobig =
    map (\(Reduct lk _ _ _) -> lk) reducts ++ reverse todo ++ reverse tobig

type Next = (Int, Seen, [LPreskel], [Int])

-- Update state variables used by step.
next :: LPreskel -> Next -> Preskel -> Next
next p (n, seen, todo, dups) k =
    let g = gist k in
    case recall (wasSeen g) seen of
      Just (_, label) ->
          (n, seen, todo, label : dups)
      Nothing ->
          (n + 1, remember (g, n) seen, lk : todo, dups)
          where
            lk = withParent k n p -- Label a preskeleton here

-- This function reduces without checking for isomorphisms
fast :: Options -> Handle -> [Preskel] -> Int -> Int -> [LPreskel] -> IO ()
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
      let shape = if null ns then Shape else Ordinary
      wrt p h (commentPreskel lk [] ns shape Nada msg)
      let (n', todo') = foldl (children lk) (n, []) ks'
      fast p h ks m n' (todo ++ reverse todo')

children :: LPreskel -> (Int, [LPreskel]) -> Preskel -> (Int, [LPreskel])
children p (n, todo) k =        -- Label a preskeleton here
    (n + 1, withParent k n p : todo)

-- Print partial results in a form that works with analysis tools
dump :: Options -> Handle -> [LPreskel] -> String -> IO ()
dump _ h [] msg =
    do
      hClose h
      abort msg
dump p h (lk : lks) msg =
    do
      let ns = unrealized $ content lk
      wrt p h (commentPreskel lk [] ns Aborted Nada "aborted")
      dump p h lks msg

-- Add a label, maybe a parent, a list of seen preskeletons isomorphic
-- to some members of this skeleton's cohort, and a list of unrealized
-- nodes.  If it's a shape, note this fact.  Add a comment if present.
commentPreskel :: LPreskel -> [Int] -> [Node] -> Kind ->
                  Anno -> String -> SExpr ()
commentPreskel lk seen unrealized kind anno msg =
    displayPreskel k $
    addKeyValues "label" [N () (label lk)] $
    maybeAddVKeyValues "parent" (\p -> [N () (label p)]) (parent lk) $
    condAddKeyValues "seen" (not $ null seen)
                     (map (N ()) (L.sort (L.nub seen))) $
    addKeyValues "unrealized" (map displayNode $ L.sort unrealized) $
    addKindKey kind $ addAnnoKey anno $
    condAddKeyValues "satisfies" (kind == Shape && (not $ null $ kgoals k))
    (satisfies k) $
    -- Structure preserving maps
    -- Added for cpsasas program
    condAddKeyValues "maps" fringe (maps k) $
    -- Nodes of origination
    -- Added for cpsasas program
    condAddKeyValues "origs" (starter k || fringe) (origs k) $
    -- Messages
    case msg of
      "" -> []
      _ -> [comment msg]
    where
      fringe = isFringe kind
      k = content lk
      starter k =               -- True for the POV skeleton and
          case pov k of         -- just a few others
            Nothing -> True
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

data Kind
    = Ordinary
    | Shape
    | Fringe
    | Aborted
      deriving (Eq, Show)

addKindKey :: Kind -> [SExpr ()] -> [SExpr ()]
addKindKey Ordinary xs = xs
addKindKey Shape xs = addKeyValues "shape" [] xs
addKindKey Fringe xs = addKeyValues "fringe" [] xs
addKindKey Aborted xs = addKeyValues "aborted" [] xs

isFringe :: Kind -> Bool
isFringe Ordinary = False
isFringe Shape = True
isFringe Fringe = True
isFringe Aborted = False

-- Skeleton annotations
data Anno
  = Nada
  | Preskeleton
  | SatisfiesAll
  | Dead

addAnnoKey :: Anno -> [SExpr ()] -> [SExpr ()]
addAnnoKey Nada xs = xs
addAnnoKey Preskeleton xs = addKeyValues "preskeleton" [] xs
addAnnoKey SatisfiesAll xs = addKeyValues "satisfies-all" [] xs
addAnnoKey Dead xs = addKeyValues "dead" [] xs

-- Variable assignments and security goals

satisfies :: Preskel -> [SExpr ()]
satisfies k =
  map f (sat k) where
    f (_, []) = S () "yes"
    f (g, e : _) =
      L () (S () "no" : displayEnv (ctx $ uvars g) (ctx $ kvars k) e)
    ctx ts = addToContext emptyContext ts

-- Prints structure preserving maps (homomorphisms)
maps :: Preskel -> [SExpr ()]
maps k =
    map (amap $ strandMap k) (envMaps k)
    where
      amap strands env = L () [L () strands, L () env]
      strandMap k = map (N ()) (map f (pprob k))
      f s = prob k !! s
      envMaps k =
          case pov k of
            Nothing -> []
            Just k' ->
                map (displayEnv (ctx k') (ctx k)) (homomorphism k' k (prob k))
      ctx k = addToContext emptyContext (kvars k)

-- Prints the nodes of origination for each uniquely originating atom
origs :: Preskel -> [SExpr ()]
origs k =
    [ L () [displayTerm ctx t, displayNode n]
      | (t, ns) <- korig k, n <- ns ]
    where
      ctx = addToContext emptyContext (kvars k)
