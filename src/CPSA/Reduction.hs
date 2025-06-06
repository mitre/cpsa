-- Term reduction for the CPSA solver.

-- Copyright (c) 2010 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

-- Provides the top-level search loop, which implements term reduction
-- on skeletons.

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
import CPSA.Operation
import CPSA.Strand
import CPSA.Cohort
import CPSA.Displayer

{--
import System.IO.Unsafe
import Control.Exception (try)
import System.IO.Error (ioeGetErrorString)

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x

zb :: Show a => a -> Bool -> Bool
zb a False = z a False
zb _ b = b

zn :: Show a => a -> Maybe b -> Maybe b
zn x Nothing = z x Nothing
zn _ y = y

zf :: Show a => a -> Bool -> Bool
zf x False = z x False
zf _ y = y

zt :: Show a => a -> Bool -> Bool
zt x True = z x True
zt _ y = y

zl :: Show a => [a] -> [a]
zl a = z (length a) a

zi :: Instance -> String
zi inst =
    show (map f e)
    where
      domain = rvars (role inst)
      e = reify domain (env inst)
      range = map snd e
      f (x, t) = (displayTerm (context domain) x,
                  displayTerm (context range) t)
      context ts = addToContext emptyContext ts

zv :: Preskel -> String
zv k =
  unsafePerformIO $ do
    y <- try $ verbosePreskelWellFormed k
    case y of
      Right _ ->
        return "preskel well formed"
      Left err ->
        return $ ioeGetErrorString err

-- Also see showst
--}

-- Set when debugging an exception so that buffered results get out.
useFlush :: Bool
useFlush = True                -- False

-- Possibly generalization is no longer needed, to find all of the
-- shapes?  To find out if this is true, and reap the benefits if it
-- is, we add the dieOnGeneralization flag.  It causes a
-- generalization step to terminate the search branch.

-- Conclusion:  generalization is definitely needed, since it can
-- remove listeners as unnecessary.  You wouldn't want every branch
-- with listeners to silently disappear when CPSA notes that they can
-- be generalized away.  ( :- )

dieOnGeneralization :: Bool
dieOnGeneralization = False -- True

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
type IPreskel = (Preskel, Int)

stronglyIsomorphic :: Preskel -> Preskel -> [Sid]
stronglyIsomorphic k1 k2 =
    loop $ findIsomorphisms (gist k1) (gist k2)
    where
      loop [] = []
      loop ((_, _, sm) : maps) =
          if unrealizedInvariant sm then
             sm
          else
             loop maps

      translateNode sidMap (s,i) = ((sidMap !! s), i)

      setsEq as bs = subset as bs &&
                     subset bs as

      unrealizedInvariant sidMap =
          setsEq (map (translateNode sidMap) $ unrealized k1)
                 $ unrealized k2

{--

-- Suppose homomorphism H has strand map sm1 and homomorphism J has
-- strand map sm2, where H's target is J's source.

-- Then the strand map of J o H is composeStrandMap sm1 sm2.

composeStrandMap :: [Sid] -> [Sid] -> [Sid]
composeStrandMap sm1 sm2 = map ((!!) sm2) sm1

--        take (min (length sm1) (length sm2))
--                (map ((!!) sm2) )
--    map ((!!) (take (L.length sm1) sm2)) sm1

--}

-- A seen history as a list.

newtype Seen = Seen [IPreskel]

-- Create a singleton seen history
hist :: IPreskel -> Seen
hist ik = Seen [ik]

-- Add an element to the seen history.
remember :: IPreskel -> Seen -> Seen
remember ik (Seen seen) = Seen (ik : seen)

-- If preskel has been seen, return its label and strand map.
recall :: Preskel -> Seen -> Maybe (Int, [Sid])
recall k (Seen seen) =
    loop seen
    where
      loop [] = Nothing
      loop ((k', n) : seen) =
          let (k1, k2) = if generalized k then
                             (k', k)
                         else
                             (k, k') in
          case stronglyIsomorphic k1 k2 of
            [] -> loop seen
            sm -> Just (n, sm)

-- Create an empty seen history
void :: Seen
void = Seen []

-- Merge two seen histories.
merge :: Seen -> Seen -> Seen
merge (Seen xs) (Seen ys) = Seen (xs ++ ys)

-- Contains the result of applying the cohort reduction rule.  The
-- ReductStable case reports a shape

-- The last position in the Reduct case is used to hold the reverse of
-- the labels of the seen children.

-- The Genlz case contains the result of a generalization step,
-- structured like a Reduct case.

data Reduct t g s e
    = ReductStable !(LPreskel)
    | Reduct !(LPreskel) !Int ![Preskel] ![SeenSkel]
    | Genlz !(LPreskel) !Int ![Preskel] ![SeenSkel]

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
              wrt p h (commentPreskel lk [] (unrealized k) Ordinary Dead -- Mark this case dead
                       "Input cannot be made into a skeleton--nothing to do")
              solve p h ks (n + 1)
        [k'] ->
            if isomorphic (gist k) (gist k') then -- Input was a skeleton
                let lk' = LPreskel k' n 0 Nothing in
                begin p h ks (n + optLimit p) (n + 1)
                         (hist (k', n)) lk'
            else                -- Input was not a skeleton
                do
                  let lk = LPreskel k n (-1) Nothing
                  wrt p h (commentPreskel lk [] (unrealized k) Ordinary
                           Preskeleton "Not a skeleton")
                  let lk' = withParent k' (n + 1) lk
                  begin p h ks (n + optLimit p) (n + 2)
                           (hist (k', n + 1)) lk'
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
        search p h ks m n' seen' (reverse todo') []

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
-- toobig holds skeletons that have exceed the strand bound.
breadth :: Options -> Handle -> [Preskel] -> Int -> Int -> Seen ->
           [LPreskel] -> [LPreskel] -> IO ()
breadth p h ks _ n _ [] [] =       -- Empty todo list and toobig list
    do
      wrt p h (comment "Nothing left to do")
      solve p h ks n            -- Solve next problem
breadth p h _ _ _ _ [] toobig = -- Empty todo list and non-null toobig list
    do
      wrt p h (comment "Strand bound exceeded--aborting run")
      dump p h (reverse toobig)  "Strand bound exceeded"
breadth p h ks m n seen todo toobig =
    step p h ks m seen n void [] toobig (parMap (branch p seen) todo)

-- Function step handles one skeleton in one level of the tree.
step :: Options -> Handle -> [Preskel] -> Int -> Seen -> Int ->
        Seen -> [LPreskel] -> [LPreskel] -> [Reduct t g s e] -> IO ()
step p h ks m oseen n seen todo toobig [] = -- Empty reducts
    breadth p h ks m n (merge seen oseen) (reverse todo) toobig
step p h _ m _ n _ todo toobig reducts
    | n > m =                   -- Check step count
        do
          wrt p h (comment "Step limit exceeded--aborting run")
          dump p h (mktodo reducts todo toobig) "Step limit exceeded"
step p h ks m oseen n seen todo toobig (Reduct lk _ _  _  : reducts)
    | nstrands (content lk) >= optBound p = -- Check strand count
        step p h ks m oseen n seen todo (lk : toobig) reducts
step p h ks m oseen n seen todo toobig (ReductStable lk : reducts) =
    case recall (content lk) seen of
      Just (_, _) ->
      --           z ("seen", label lk) $
          step p h ks m oseen n seen todo toobig reducts
      Nothing ->
          do
            wrt p h (commentPreskel lk [] [] Shape Nada "")
      -- z ("unseen", label lk) $
            step p h ks m oseen n seen todo toobig reducts

step p h ks m oseen n seen todo toobig (Genlz lk size kids dups : reducts)
    | dieOnGeneralization =
        do
          let ns = unrealized (content lk)
          wrt p h (commentPreskel lk [] ns Ordinary Dead "died of generalization")
          step p h ks m oseen n seen todo toobig reducts
    | otherwise =
      step p h ks m oseen n seen todo toobig (Reduct lk size kids dups : reducts)

step p h ks m oseen n seen todo toobig (Reduct lk size kids dups : reducts)
    | optGoalsSat p && satCheck lk = -- Stop if goals satisfied mode?
        do
          let ns = unrealized (content lk)
          let shape = if null ns then Shape else Fringe
          wrt p h (commentPreskel lk [] ns shape SatisfiesAll "satisfies all")
          step p h ks m oseen n seen todo toobig reducts
    | size <= 0 =               -- Interpret empty reducts
        do
          let ns = unrealized (content lk)
              -- let shape = null ns
              --             case shape of
              --               True -> wrt p h (commentPreskel lk [] ns Shape Nada "")
              --               False  ->
          wrt p h (commentPreskel lk [] ns Ordinary Dead "empty cohort")
          step p h ks m oseen n seen todo toobig reducts
    | optDepth p > 0 && depth lk >= optDepth p =
        do
          let ns = unrealized (content lk)
          wrt p h (commentPreskel lk [] ns Fringe Nada "")
          step p h ks m oseen n seen todo toobig reducts
    | otherwise =
        do
          let (n', seen', todo', dups') =
                  foldl (next lk) (n, seen, todo, dups) kids
          let ns = unrealized (content lk)
          let u = size - length dups'
          let msg = shows size $ showString " in cohort - " $
                         shows u " not yet seen"
          wrt p h (commentPreskel lk (reverse dups') ns Ordinary Nada msg)
          step p h ks m oseen n' seen' todo' toobig reducts

-- Expands one branch in the derivation tree.
branch :: Options -> Seen -> LPreskel -> Reduct t g s e
branch p seen lk =
    case reduce (mkMode p) (content lk) of
      Stable -> ReductStable lk
      Crt kids ->
          Reduct lk (length kids) (seqList $ reverse unseen) (seqList dups)
        where
          (unseen, dups) =
              foldl (duplicates seen) ([], []) kids
      Gnl kids ->
          Genlz lk (length kids) (seqList $ reverse unseen) (seqList dups)
        where
          (unseen, dups) =
              foldl (duplicates seen) ([], []) kids

mkMode :: Options -> Mode
mkMode p =
    Mode { noGeneralization = optNoIsoChk p,
           nonceFirstOrder = optCheckNoncesFirst p,
           visitOldStrandsFirst = optTryOldStrandsFirst p,
           reverseNodeOrder = optTryYoungNodesFirst p}

-- The Seen skeleton's label with the duplicate skeleton
type SeenSkel = (Int, Preskel)

duplicates :: Seen -> ([Preskel], [SeenSkel]) -> Preskel ->
              ([Preskel], [SeenSkel])
duplicates seen (unseen, dups) kid =
    case recall kid seen of
      Just (label, sm) -> (unseen, maybeAdd (label, fixStrandMap kid sm) dups)
      Nothing -> (kid : unseen, dups)
    where
      maybeAdd (i,k) [] = [(i,k)]
      maybeAdd (i,k) ((j,k') : rest) =
          if i<j then (i,k) : (j,k') : rest
          else if i == j then (j,k') : rest
               else (j,k') : maybeAdd (i,k) rest

fixStrandMap :: Preskel -> [Sid] -> Preskel
fixStrandMap k _ = k 

{--
  fixStrandMap k sm =
    updateStrandMap (composeStrandMap -- sm1 sm2
                     (if sm1Challenging sm1
                      then (z ("sm1 is challenging: " ++ (show sm1) ++
                               (if generalized k
                                then " generalizing "
                                else " ") ++
                               (show sm2))
                            sm1)
                      else sm1)
                     sm2)
    k
    where
      (sm1, sm2) =
          if generalized k then
              (sm, getStrandMap kop)
          else
            (getStrandMap kop, sm)
      kop = operation k
      sm1Challenging = any ((<=) (L.length sm))
      --}

generalized :: Preskel -> Bool
generalized k =
    case operation k of
      Generalized _ _ -> True
      _ -> False

-- Make a todo list for dump
mktodo :: [Reduct t g s e] -> [LPreskel] -> [LPreskel] -> [LPreskel]
mktodo reducts todo toobig =
    foldl f [] reducts ++ reverse todo ++ reverse toobig
    where
      f sofar (Reduct lk _ _ _) = lk : sofar
      f sofar (Genlz lk _ _ _) = lk : sofar
      f sofar (ReductStable lk) = lk : sofar

type Next = (Int, Seen, [LPreskel], [SeenSkel])

-- Update state variables used by step.
next :: LPreskel -> Next -> Preskel -> Next
next p (n, seen, todo, dups) k =
    case recall k seen of
      Just (label, sm) ->
          (n, seen, todo, (label, fixStrandMap k sm) : dups)
      Nothing ->
          (n + 1, remember (k, n) seen, lk : todo, dups)
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
      let red = reduce (mkMode p) (content lk)
      let (len,ks') = (case red of
                   Stable -> (0,[])
                   Crt kids -> (length kids, kids)
                   Gnl kids -> (length kids, kids))
      let msg = show len ++ " in cohort"
      let shape = (case red of
                     Stable -> Shape
                     Crt _ -> Ordinary
                     Gnl _ -> Ordinary)
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
commentPreskel :: LPreskel -> [SeenSkel] -> [Node] -> Kind ->
                  Anno -> String -> SExpr ()
commentPreskel lk seen unrealized kind anno msg =
    let realizedToken = case (null unrealized) of
                          True -> "realized"
                          False -> "unrealized" in
    displayPreskel k $
    addKeyValues "label" [N () (label lk)] $
    maybeAddVKeyValues "parent" (\p -> [N () (label p)]) (parent lk) $
    condAddKeyValues "seen" (not $ null sortedSeen)
                     (map (N () . fst) sortedSeen) $
    condAddKeyValues "seen-ops" (not $ null sortedSeen)
                     (map displaySeen sortedSeen) $
    addKeyValues realizedToken (map displayNode $ L.sort unrealized) $
    addKindKey kind $ addAnnoKey anno $
    condAddKeyValues "satisfies" (kind == Shape && (not $ null $ kgoals k))
    (satisfies k) $
    -- Structure preserving maps
    -- Added for cpsasas program
    condAddKeyValues "maps" fringe (maps k) $
    -- Nodes of origination
    -- Added for cpsasas program
    condAddKeyValues "origs" (starter k || fringe) (origs k) $
    condAddKeyValues "ugens" (not (null (gens k)) &&
                                      (starter k || fringe))
                         (gens k) $
    -- Messages
    case msg of
      "" -> []
      _ -> [comment msg]
    where
      fringe = isFringe kind
      k = content lk
      sortedSeen = L.sortOn fst seen
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

displaySeen :: SeenSkel -> SExpr ()
displaySeen (label, k) =
    L () (N () label : displayOperation k ctx
                (displayStrandMap k []))
    where
      ctx = varsContext vars
      vars = kfvars k ++ kvars k

-- Variable assignments and security goals

satisfies :: Preskel -> [SExpr ()]
satisfies k =
  map f (sat k) where
    f (_, []) = S () "yes"
    f (g, ge : _) =
      L () (S () "no" :
            (displayForm
             (ctx $ (uvars g) ++ (evars g) ++ (kvars k))
             (unSatReport k g ge)) :
            (displayEnv (ctx $ uvars g) (ctx $ kvars k) (snd ge)))
    ctx ts = addToContext emptyContext ts
    evars g = concatMap fst $ consq g

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
                map (displayEnvSansPts vars (ctx k') (ctx k)) (homomorphism k' k (prob k))
      ctx k = addToContext emptyContext (kvars k)
      vars = kvars k

-- Prints the nodes of origination for each uniquely originating atom
origs :: Preskel -> [SExpr ()]
origs k =
    [ L () [displayTerm ctx t, displayNode n]
      | (t, ns) <- korig k, n <- ns ]
    where
      ctx = addToContext emptyContext (kvars k)

-- Prints the nodes of generation for each uniquely generated atom
gens :: Preskel -> [SExpr ()]
gens k =
    [ L () [displayTerm ctx t, displayNode n]
      | (t, ns) <- kugen k, n <- ns ]
    where
      ctx = addToContext emptyContext (kvars k)

satCheck :: LPreskel -> Bool
satCheck lk =
  not (null tests) && all f tests
  where
    tests = sat $ content lk
    f (_, []) = True
    f _ = False
