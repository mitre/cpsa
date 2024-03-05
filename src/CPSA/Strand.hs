-- Instance and preskeleton data structures and support functions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Strand (Instance, mkInstance, bldInstance, mkListener,
    role, env, trace, height, listenerTerm, Sid, Node, mkPreskel,
    firstSkeleton, Pair, Preskel, gen, protocol, kgoals, insts, orderings,
    pov, knon, kpnon, kunique, kuniqgen, kabsent, kprecur, kgenSt,
    kconf, kauth, kfacts, korig, kugen, kpriority, kcomment, nstrands,
    kvars, kfvars, strandids, kterms, kchans, uniqOrig, uniqGen,
    preskelWellFormed, confCm, authCm,
    verbosePreskelWellFormed, Strand, inst, sid, nodes,
    Vertex, strand, pos, preds, event, graphNode, strands, vertex,
    Gist, gist, isomorphic, factorIsomorphicPreskels, contract, augment,
    inheritRnon, inheritRpnon, inheritRunique, inheritRuniqgen, inheritRabsent,
    inheritRconf, inheritRauth, addListener, addBaseListener, addAbsence,
    Cause (..), Direction (..), Method (..), Operation (..),
    operation, krules, pprob, prob, homomorphism, toSkeleton, generalize,
    collapse, sat, unSatReport, FTerm (..), Fact (..), simplify, rewrite,
    localSignal, rewriteUnaryOneOnce, nodePairsOfSkel, applyLeadsTo) where

import Control.Monad
import Control.Parallel
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Maybe as M
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Channel
import CPSA.Protocol

{--

import System.IO.Unsafe
import Control.Exception (try)
import System.IO.Error (ioeGetErrorString)

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x

zShow :: Show a => a -> a
zShow x = z (show x) x

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

-- Compile time switches for expermentation.

-- Do not do multistrand thinning.
useSingleStrandThinning :: Bool
useSingleStrandThinning = False -- True

-- Sanity check: ensure no role variable occurs in a skeleton.
useCheckVars :: Bool
useCheckVars = False -- True

useThinningDuringCollapsing :: Bool
useThinningDuringCollapsing = False -- True

useThinningWhileSolving :: Bool
useThinningWhileSolving = True -- False

useNoOrigPreservation :: Bool
useNoOrigPreservation = False -- True

-- Use Pruning instead of thinning
usePruning :: Bool
usePruning = False -- True

-- When using pruning use strong version
useStrongPruning :: Bool
useStrongPruning = True -- False

-- Check terms in preskeletons, should be off by default
useWellFormedTerms :: Bool
useWellFormedTerms = False -- True

-- Don't do variable separation if False
useVariableSeparation :: Bool
useVariableSeparation = True -- False

-- Instances and Strand Identifiers

-- An Instance is an instance of a role, in the sense that each
-- variable in the role's trace has been replaced by a term.  The
-- trace of the instance might be shorter that the role's trace, but
-- only truncating nodes from the end of the trace.

-- A preskeleton stores its strands as a ordered sequence of
-- instances.  A strand is the position of an instance in the
-- sequence.  Duplicates are allowed in the sequence, as two strands
-- can be instantiated from the same role in the same way.

type Sid = Int                  -- Strand Identifier

data Instance = Instance
    { role :: Role,             -- Role from which this was
                                -- instantiated

      env :: !Env,              -- The environment used to build this
                                -- instance's trace from its role's
                                -- trace

      trace :: !Trace,          -- Instance's trace

      height :: !Int }          -- Height of the instance
    deriving Show

-- Create a fresh instance of the given height.  The environment
-- specifies how to map some variables in the role's trace.  Unmapped
-- variables are instantiated with fresh variables to avoid naming
-- conflicts.
mkInstance :: Gen -> Role -> Env -> Int -> (Gen, Instance)
mkInstance gen role env height =
    let trace = rtrace role
        rheight = length trace in
    if height < 1 || height > rheight then
        error "Strand.mkInstance: Bad strand height"
    else
        let (gen', env') = grow (rvars role) gen env
            trace' = map (evtMap $ instantiate env') (take height trace) in
        -- Ensure every variable in the range of the environment
        -- occurs in the trace.
        case bldInstance role trace' gen' of
          (gen'', inst) : _ -> (gen'', inst)
          [] -> error "Strand.mkInstance: Not an instance"

-- For each term that matches itself in the environment, extend the
-- mapping so that the term maps to one with a fresh set of variables.
-- It is an error if a variable in one of the terms is explicitly
-- mapped to itself in the initial environment.
grow :: [Term] -> Gen -> Env -> (Gen, Env)
grow [] gen env = (gen, env)
grow (t : ts) gen env =
    case match t t (gen, env) of
      [] -> grow ts gen env     -- Term already mapped
      _ ->                      -- Otherwise make a fresh mapping
          let (gen', t') = clone gen t in
          case match t t' (gen', env) of
            (gen'', env') : _ -> grow ts gen'' env'
            [] -> error "Strand.grow: Internal error"

-- Build an instance from a role and a trace.  Returns the empty list
-- if the trace is not an instance of the given role.
bldInstance :: Role -> Trace -> Gen -> [(Gen, Instance)]
bldInstance _ [] _ = error "Strand.bldInstance: Bad trace"
bldInstance role trace gen =
    loop (rtrace role) trace (gen, emptyEnv) -- Loop builds env
    where
      loop _ [] (gen, env) =        -- Trace can be shorter than role's trace
          [(gen, makeInstance role env trace)]
      loop (In t : c) (In t' : c') ge =
          do
            env <- cmMatch t t' ge
            loop c c' env
      loop (Out t : c) (Out t' : c') ge =
          do
            env <- cmMatch t t' ge
            loop c c' env
      loop _ _ _ = []

makeInstance :: Role -> Env -> Trace -> Instance
makeInstance role env trace =
    Instance { role = role,
               env = env,
               trace = trace,
               height = length trace }

mkListener :: Prot -> Gen -> Term -> (Gen, Instance)
mkListener p gen term =
    case bldInstance (listenerRole p) [In $ Plain term, Out $ Plain term] gen of
      [x] -> x
      _ -> error "Strand.mkListener: Cannot build an instance of a listener"

-- Add to set s the variables that are in the range of instance i
addIvars :: Set Term -> Instance -> Set Term
addIvars s i =
    foldl g s (reify (rvars (role i)) (env i))
    where
      g s (_, t) = foldVars (flip S.insert) s t

listenerTerm :: Instance -> Maybe Term
listenerTerm inst =
    case rname (role inst) of
      "" ->
        do
          cm <- inbnd (trace inst !! 0) -- Get first term in trace
          case cm of
            Plain t -> Just t
            ChMsg _ _ -> Nothing
      _ -> Nothing              -- Not a listener strand

-- Nodes, Pairs, and Graphs

-- A node is composed of two integers, a strand identifier and a
-- position.  The position identifies an event in the strand's trace.
-- The second integer must be non-negative and less than the strand's
-- height

type Node = (Sid, Int)

-- A pair gives an ordering of two nodes, meaning the first node is
-- before the second one.

type Pair = (Node, Node)

-- Graphs of preskeletons

-- A strand is what is referred to by a strand ID.

data GraphStrand e i                 -- e for event, i for instance
    = GraphStrand { inst :: i,
                    nodes :: [GraphNode e i],
                    sid :: Sid }

-- The Strand ID determines equality and orderings
instance Eq (GraphStrand e i) where
    s0 == s1 = sid s0 == sid s1

instance Ord (GraphStrand e i) where
    compare s0 s1 = compare (sid s0) (sid s1)

instance Show (GraphStrand e i) where
    showsPrec _ s = shows (sid s)

-- A vertex is what is referred to by a node.

data GraphNode e i                 -- e for event, i for instance
    = GraphNode { event :: e,
                  preds :: [GraphNode e i], -- Immediate preds including
                  strand :: GraphStrand e i,  -- strand succession edges
                  pos :: Int }  -- The position of the node in the strand

-- The node determines equality and orderings
instance Eq (GraphNode e i) where
    n0 == n1 = (strand n0, pos n0) == (strand n1, pos n1)

instance Ord (GraphNode e i) where
    compare n0 n1 = compare (strand n0, pos n0) (strand n1, pos n1)

instance Show (GraphNode e i) where
    showsPrec _ n = let (s, i') = graphNode n in
                    showChar '(' . shows s . showString ", " .
                    shows i' . showChar ')'

-- The node of a vertex
graphNode :: GraphNode e i -> Node
graphNode n = (sid (strand n), pos n)

type GraphEdge e i = (GraphNode e i, GraphNode e i)

-- The pair of an edge
graphPair :: GraphEdge e i -> Pair
graphPair (n0, n1) = (graphNode n0, graphNode n1)

graphEdges :: [GraphStrand e i] -> [GraphEdge e i]
graphEdges strands =
    [ (dst, src) | s <- strands, src <- nodes s, dst <- preds src ]

data Graph e i
    = Graph { gstrands :: [GraphStrand e i],
              gedges :: [GraphEdge e i] }

-- The graph associated with a preskeleton
graph :: (i -> [d]) -> (i -> Int) -> [i] -> [Pair] -> Graph d i
graph trace height insts pairs =
    Graph { gstrands = strands,
            gedges = map getEdge pairs }
    where
      strands = [ GraphStrand { inst = inst,
                                nodes = nodes !! sid,
                                sid = sid } |
                  (sid, inst) <- zip [0..] insts ]
      nodes = [ [ GraphNode { event = trace (inst strand) !! pos,
                              preds = preds (sid, pos),
                              strand = strand,
                              pos = pos } |
                  pos <- nats (height (inst strand)) ] |
                (sid, strand) <- zip [0..] strands ]
      preds n = map getNode (entry n)
      getNode (s, i) = nodes !! s !! i
      getEdge (n0, n1) = (getNode n0, getNode n1)
      entry n = enrich n [ n0 | (n0, n1) <- pairs, n1 == n ]
      -- add strand succession edges
      enrich (s, i) ns
          | i > 0 = (s, i - 1) : ns
          | otherwise = ns

-- Does start node precede end node?
graphPrecedes :: GraphNode e i -> GraphNode e i -> Bool
graphPrecedes start end =
    let predecessors = preds end in
    any (== start) predecessors || any (graphPrecedes start) predecessors

-- Compute the transitive reduction
graphReduce :: [GraphEdge e i] -> [GraphEdge e i]
graphReduce orderings =
    filter essential orderings
    where
      essential (dst, src) =
          loop dst (L.delete dst (preds src)) [src]
      loop _ [] _ = True        -- No other path found
      loop dst (n : ns) seen
          | n == dst = False    -- There is another path
          | elem n seen = loop dst ns seen
          | otherwise = loop dst (preds n ++ ns) (n : seen)

-- Compute the transitive closure, but omit same strand pairs.
-- This routine returns pairs that are not well ordered.
-- Deal with it!
graphClose :: [GraphEdge e i] -> [GraphEdge e i]
graphClose orderings =
    filter (not . sameStrands) (loop orderings False orderings)
    where
      loop orderings False [] = orderings
      loop orderings True [] =
          loop orderings False orderings -- restart loop
      loop orderings repeat ((n0, n1) : pairs) =
          inner orderings repeat pairs [(n, n1) | n <- preds n0]
      inner orderings repeat pairs [] =
          loop orderings repeat pairs
      inner orderings repeat pairs (p : rest)
          | elem p orderings = inner orderings repeat pairs rest
          | otherwise = inner (p : orderings) True pairs rest
      sameStrands (n0, n1) = strand n0 == strand n1

-- Compute the transitive closure including same strand
-- pairs.
-- This routine returns pairs that are not well ordered.
-- Deal with it!
graphCloseAll :: [GraphEdge e i] -> [GraphEdge e i]
graphCloseAll orderings =
    graphAllCloseLoop orderings False orderings

graphAllCloseLoop :: [GraphEdge e i] -> Bool -> [GraphEdge e i] -> [GraphEdge e i]
graphAllCloseLoop orderings False [] = orderings
graphAllCloseLoop orderings True [] = graphAllCloseLoop orderings False orderings -- restart loop
graphAllCloseLoop orderings repeat ((n0, n1) : pairs) =
    inner orderings repeat pairs [(n, n1) | n <- preds n0]
    where
      inner orderings repeat pairs [] =
          graphAllCloseLoop orderings repeat pairs
      inner orderings repeat pairs (p : rest)
          | elem p orderings = inner orderings repeat pairs rest
          | otherwise = inner (p : orderings) True pairs rest

-- Shared part of preskeletons

data Shared = Shared
    { prot  :: Prot,
      goals :: [Goal] }

instance Show Shared where
    showsPrec _ s = shows (prot s)

protocol :: Preskel -> Prot
protocol k = prot $ shared k

kgoals :: Preskel -> [Goal]
kgoals k = goals $ shared k

-- Preskeletons

data Preskel = Preskel
    { gen :: !Gen,
      shared :: Shared,
      insts :: ![Instance],
      strands :: ![Strand],
      orderings :: ![Pair],
      kgpOrds :: [Pair],
      kgpOrdsAll :: [Pair],
      edges :: ![Edge],
      knon :: ![Term],            -- A list of atoms
      kpnon :: ![Term],           -- A list of atoms
      kunique :: ![Term],         -- A list of atoms
      kuniqgen :: ![Term],        -- A list of atoms
      kabsent :: ![(Term, Term)], -- A list of pairs of terms
      kprecur :: ![Node],         -- A list of nodes
      kgenSt :: ![Term],          -- A list of terms, known to be non-initial
      kconf :: ![Term],           -- A list of channels
      kauth :: ![Term],           -- A list of channels
      kfacts :: ![Fact],          -- A list of facts
      kfvars :: [Term],           -- Fact vars not in instances
      kpriority :: [(Node, Int)], -- Override node priority
      kcomment :: [SExpr ()],   -- Comments from the input
      korig :: ![(Term, [Node])], -- This is an association list with a
                                -- pair for each element of kunique.
                                -- The value associated with a term
                                -- is a list of the nodes at which it
                                -- originates--the term's provenance.
      kugen :: ![(Term, [Node])], -- Like korig but for kuniqgen.
      pov :: Maybe Preskel,     -- Point of view, the
                                -- original problem statement.
      strandids :: ![Sid],
      tc :: [Pair],             -- Transitive closure of orderings
                                -- Used only during generalization
      kgist :: Gist,            -- Gist for iso checking
      operation :: Operation,
      krules :: [String],    -- Names of rules applied
      pprob :: [Sid],        -- strand map from preskel to first skeleton
      prob :: [Sid] }        -- A map from the strands in the original
    deriving Show               -- problem statement, the pov, into
                                -- these strands.

-- The pov skeleton is the only skeleton that should have Nothing in
-- its pov field.

type Strand = GraphStrand Event Instance

type Vertex = GraphNode Event Instance

type Edge = GraphEdge Event Instance

-- Data structure for tracking the causes for the creation of
-- preskeletons.

data Cause
    = Cause Direction Node CMT (Set CMT)
    deriving Show

data Direction = Encryption | Nonce | Channel deriving Show

data Method
    = Deleted Node
    | Weakened Pair
    | Separated Term
    | Forgot Term
    deriving Show

-- The operation used to generate the preskeleteton is either new via
-- the loader, a contraction, a regular augmentation, a listener
-- augmentation, or a mininization.  The augmentation includes a role
-- name and instance height.
data Operation
    = New
    | Contracted Subst Cause
    | Displaced Int Int String Int Cause
    | AddedStrand String Int Cause
    | AddedListener Term Cause
    | AddedAbsence Term Term Cause
    | Generalized Method
    | Collapsed Int Int
      deriving Show

-- Create a preskeleton.  The point of view field is not filled in.
-- This version is exported for use by the loader.  This preskeleton
-- must be consumed by firstSkeleton.
mkPreskel :: Gen -> Prot -> [Goal] -> [Instance] -> [Pair] ->
             [Term] -> [Term] -> [Term] -> [Term] ->
             [(Term, Term)] -> [Node] -> [Term] -> [Term] ->
             [Term] -> [Fact] -> [(Node, Int)] -> [SExpr ()] -> Preskel
mkPreskel gen protocol gs insts orderings non pnon
          unique uniqgen absent precur genStVs
          conf auth facts prio comment =
    k { kcomment = comment }
    where
      k = newPreskel gen shared insts orderings non pnon
          unique uniqgen absent precur genStVs
          conf auth facts prio New [] prob prob Nothing
      shared = Shared { prot = protocol, goals = gs }
      prob = strandids k        -- Fixed point on k is okay.

-- Strand functions

strandInst :: Preskel -> Sid -> Instance
strandInst k strand =
    let strands = insts k in
    if strand < L.length strands then (strands !! strand)
    else error ("strandInst:  index " ++ (show strand) ++ " is too big for " ++ (show (insts k)))

nstrands :: Preskel -> Int
nstrands k = length (strandids k)

-- Convert the preskeleton made by the loader into the first skeleton
-- used in the search.
firstSkeleton :: Preskel -> [Preskel]
firstSkeleton k =
    do
      k <- wellFormedPreskel k
      k' <- toSkeleton False k   -- only k' should have pov = Nothing
      return $ k' { pprob = prob k', prob = strandids k', pov = Just k' }

-- Create a preskeleton.  The node ordering relation is put into the
-- preds field of each instance in this function.  The maybe uniquely
-- originating term data is also filled in.  This version is used
-- within this module.
newPreskel :: Gen -> Shared ->
             [Instance] -> [Pair] -> [Term] -> [Term] -> [Term] ->
             [Term] -> [(Term, Term)] -> [Node] -> [Term] -> [Term] ->
             [Term] -> [Fact] -> [(Node, Int)] -> Operation ->
             [String] -> [Sid] -> [Sid] -> Maybe Preskel -> Preskel
newPreskel gen shared insts orderings non pnon unique
           uniqgen absent precur genSt conf auth facts
           prio oper rules pprob prob pov =
    let orderings' = L.nub orderings
        unique' = L.nub unique
        uniqgen' = L.nub uniqgen
        facts' = L.nub facts
        g = graph trace height insts orderings'
        strands = gstrands g
        edges = gedges g
        gpOrds = map graphPair $ graphClose $ graphEdges $ strands
        gpOrdsAll = map graphPair $ graphCloseAll $ graphEdges $ strands
        orig = map (originationNodes strands) unique'
        ugen = map (generationNodes strands) uniqgen'
        tc = filter pairWellOrdered (graphClose $ graphEdges strands)
        gg = mkGist k
        k = Preskel { gen = gen,
                      shared = shared,
                      insts = insts,
                      strands = strands,
                      orderings = orderings',
                      kgpOrds = gpOrds,
                      kgpOrdsAll = gpOrdsAll,
                      edges = edges,
                      knon = L.nub non,
                      kpnon = L.nub pnon,
                      kunique = unique',
                      kuniqgen = uniqgen',
                      kabsent = L.nub absent,
                      kprecur = L.nub precur,
                      kgenSt = L.nub genSt,
                      kconf = L.nub conf,
                      kauth = L.nub auth,
                      kfacts = facts',
                      kfvars = factVars insts facts',
                      kpriority = prio,
                      kcomment = [],
                      korig = orig,
                      kugen = ugen,
                      tc = map graphPair tc,
                      kgist = gg,
                      strandids = nats (length insts),
                      operation = oper,
                      krules = rules,
                      pprob = pprob,
                      prob = prob,
                      pov = pov } in
        if useCheckVars then
            checkVars k
        else k
{-
          if chkFacts k then k
          else k
-}

{--
  checkPOV :: Preskel -> Preskel
checkPOV k =
    case pov k of
      Nothing -> k
      Just k0 ->
          if L.length (insts k0) == L.length (prob k)
          then k
          else (z ("skel's POV has " ++ (show (L.length (insts k0)))
                   ++ " insts, but its prob has length "
                   ++ (show (L.length (prob k))))
                k)
--}

-- Suppose that a Preskel k has been created by rebinding some fields
-- in an earlier skeleton.  The fields that newPreskel would compute
-- so that they have an invariant relation to the given fields may no
-- longer satisfy that relation.

-- In this case, we call renewPreskel which will call newPreskel on
-- the freely varying fields to recompute the dependent fields.

renewPreskel :: Preskel -> Preskel
renewPreskel k =
    let k' = newPreskel
             (gen k)
             (shared k)
             (insts k)
             (orderings k)
             (knon k)
             (kpnon k)
             (kunique k)
             (kuniqgen k)
             (kabsent k)
             (kprecur k)
             (kgenSt k)
             (kconf k)
             (kauth k)
             (kfacts k)
             (kpriority k)
             (operation k)
             (krules k)
             (pprob k)
             (prob k)
             (pov k) in
    k' { kcomment = kcomment k}

checkVars :: Preskel -> Preskel
checkVars k =
    foldl f k rolevars
    where
      skelvars = S.fromList $ kvars k
      rolevars = concatMap (rvars . role) (insts k)
      f k v
        | S.member v skelvars =
            error ("Strand.checkVars: role var in skel " ++ show k)
        | otherwise = k

vertex  :: Preskel -> Node -> Vertex
vertex k (s, i) =
    nodes (strands k !! s) !! i

originationNodes :: [Strand] -> Term -> (Term, [Node])
originationNodes strands u =
    (u, [ (sid strand, p) |
          strand <- reverse strands,
          p <- M.maybeToList $ originationPos u (trace (inst strand)) ])

generationNodes :: [Strand] -> Term -> (Term, [Node])
generationNodes strands u =
    (u, [ (sid strand, p) |
          strand <- reverse strands,
          p <- M.maybeToList $ generationPos u (trace (inst strand)) ])

uniqOrig :: Preskel -> [Term]
uniqOrig k =
    do
      (t, [_]) <- reverse (korig k)
      return t

uniqGen :: Preskel -> [Term]
uniqGen k =
    do
      (t, [_]) <- reverse (kugen k)
      return t

{--
originatingStrands :: Preskel -> Term -> [Sid]
originatingStrands k t =
    let (_,nodes) = originationNodes (strands k) t in
    map (\(s,_) -> s) nodes
--}

genOrigMatch :: Term -> Node -> Node -> Bool
genOrigMatch _ (s,_) (s',_) | s == s' = True
genOrigMatch _ _ _ | otherwise =
--       z ("genOrigMatch:  Whoa, mismatch for " ++ (show u) ++ ", gen strand " ++
--          (show (s,i)) ++ " vs orig strand " ++ (show (s',i')))
      False

ugensPlusInverses :: Preskel -> [(Term, [Node])]
ugensPlusInverses k =
    concatMap
    (\(u,gNodes) -> maybe [(u,gNodes)]
                    (\u' -> [(u,gNodes), (u', gNodes)])
                    (invertKey u))
    (kugen k)

ugenGoodOrig :: Preskel -> Bool
ugenGoodOrig k =
    and
    [ genOrigMatch u gNode oNode |
      (u,gNodes) <- ugensPlusInverses k,
      gNode <- gNodes,
      oNode <- origs u ]
    where
      origs v = snd (originationNodes (strands k) v)

--    (maybe [] (\u' -> origs u')
--                    (invertKey u)) ++

--       (\(u,genNodes) -> all (all genOrigMatch u genNode)
--                        (snd (originationNodes (strands k) u)))

--       all f (kugen k)
--       where
--         f (u,gens) = all (\s -> all
--                                 (\(s',_) -> s == s')
--                                 gens)
--                      $ originatingStrands k u

--         f (u,gens) = error ("ugenGoodOrig:  Weirdly, " ++ (show u) ++
--                             " generated at wrong number of nodes " ++ (show gens) ++
--                             " in " ++ (show k))

-- A preskeleton is well formed if the ordering relation is acyclic,
-- each atom declared to be uniquely-originating is carried in some
-- preskeleton term, and every variable that occurs in each base term
-- declared to be non-originating or pen-non-originating occurs in
-- some preskeleton term, and the atom must never be carried by any
-- term, and every uniquely originating role term mapped by an
-- instance is mapped to a term that originates on the instance's
-- strand.

preskelWellFormed :: Preskel -> Bool
preskelWellFormed k =
    varSubset (knon k) terms &&
    varSubset (kpnon k) terms &&
    all nonCheck (knon k) &&
    all uniqueCheck (kunique k) &&
    all uniqgenCheck (kuniqgen k) &&
    all absentCheck (kabsent k) &&
    all genStCheck (kgenSt k) &&
    all chanCheck (kconf k) &&
    all chanCheck (kauth k) &&
    wellOrdered k && acyclicOrder k &&
    roleOrigCheck k &&
    roleGenCheck k &&
    True -- (ugenGoodOrig k || True)
    where
      terms = kterms k
      vs = kvars k
      f b t = b && t `elem` vs
      nonCheck t = all (not . carriedBy t) terms
      uniqueCheck t = any (carriedBy t) terms
      uniqgenCheck t = any (constituent t) terms
      absentCheck (x, y) = varSubset [x, y] vs && x /= y
      genStCheck t = foldVars f True t
      chanCheck c = elem c vs

-- Do notation friendly preskeleton well formed check.
wellFormedPreskel :: MonadFail m => Preskel -> m Preskel
wellFormedPreskel k
    | preskelWellFormed k && traceWellFormed k = return k
    | otherwise = fail "preskeleton not well formed"

traceWellFormed :: Preskel -> Bool
traceWellFormed k =
  not useWellFormedTerms || termsWellFormed (kterms k)

-- A version of preskelWellFormed that explains why a preskeleton is
-- not well formed.
verbosePreskelWellFormed :: MonadFail m => Preskel -> m ()
verbosePreskelWellFormed k =
    do
      failwith "a variable in non-orig is not in some trace"
                   $ varSubset (knon k) terms
      failwith "a variable in pen-non-orig is not in some trace"
                   $ varSubset (kpnon k) terms
      mapM_ nonCheck $ knon k
      mapM_ uniqueCheck $ kunique k
      mapM_ uniqgenCheck $ kuniqgen k
      mapM_ absentCheck $ kabsent k
      mapM_ genStCheck $ kgenSt k
      mapM_ confCheck $ kconf k
      mapM_ authCheck $ kauth k
      failwith "ordered pairs not well formed" $ wellOrdered k
      failwith "cycle found in ordered pairs" $ acyclicOrder k
      failwith "an inherited unique doesn't originate in its strand"
                   $ roleOrigCheck k
      failwith "an inherited unique gen doesn't generate in its strand"
                   $ roleGenCheck k
    where
      terms = kterms k
      nonCheck t =
          failwith (showString "non-orig " $ showst t " carried")
                       $ all (not . carriedBy t) terms
      uniqueCheck t =
          failwith (showString "uniq-orig " $ showst t " not carried")
                       $ any (carriedBy t) terms
      uniqgenCheck t =
          failwith (showString "uniq-gen " $ showst t " does not occur")
                       $ any (constituent t) terms
      absentCheck (x, y) =
          do
            failwith (showString "absent " $ showst x " does not occur")
                       $ elem x $ kvars k
            failwith (showString "absent " $ showst y " does not occur")
                       $ varSubset [y] (kvars k)
      genStCheck t =
          failwith (showString "gen-st " $ showst t " not carried")
                       $ any (carriedBy t) terms
      confCheck c =
        failwith (showString "confidential channel "
                  $ showst c " not in some strand")
                 $ elem c (kvars k)
      authCheck c =
        failwith (showString "authenticated channel "
                  $ showst c " not in some strand")
                 $ elem c (kvars k)

failwith :: MonadFail m => String -> Bool -> m ()
failwith msg test =
    case test of
      True -> return ()
      False -> fail msg

showst :: Term -> ShowS
showst t =
    shows $ displayTerm (addToContext emptyContext [t]) t

-- Do the nodes in the orderings have the right direction?
wellOrdered :: Preskel -> Bool
wellOrdered k =
    all pairWellOrdered (edges k)

pairWellOrdered :: Edge -> Bool
pairWellOrdered (n0, n1) =
    case (event n0, event n1) of
      (Out _, In _) -> True
      _ -> False

data Dir = Recv | Send

dirChMsgOfNode :: Node -> Preskel -> Maybe (Dir, ChMsg )
dirChMsgOfNode (i, j) k =
    do
      s <- maybeNth (strands k) i
      gn <- maybeNth (nodes s) j
      return (case event gn of
                In chMsg -> (Recv, chMsg)
                Out chMsg -> (Send, chMsg))

genNodes :: Preskel -> [Node]
genNodes k =
    let strs = strands k in
    let strCnt = L.length strs in
    [(i,j) | i <- [0..strCnt-1],
                  j <- [0 .. (L.length (nodes (strs !! i)))-1] ]

--   genSids :: Preskel -> [Sid]
--   genSids k = [0 .. (L.length (strands k))-1]

--   nodesOfSid :: Preskel -> Sid -> [Node]
--   nodesOfSid k i =
--       let strs = strands k in
--       let strCnt = L.length strs in
--       case i < strCnt of
--         True -> [(i,j) | j <- [0 .. (L.length (nodes (strs !! i)))-1] ]
--         False -> []

-- The terms used in the strands in this preskeleton.
-- Should this return a set, or a multiset?
kterms :: Preskel -> [Term]
kterms k = iterms (insts k)

-- The terms used in a list of instances.
iterms :: [Instance] -> [Term]
iterms insts =
  L.nub [evtTerm evt | i <- insts, evt <- trace i]

-- The channels used in the strands in this preskeleton.
kchans :: Preskel -> [Term]
kchans k = ichans (insts k)

-- The terms used in a list of instances.
ichans :: [Instance] -> [Term]
ichans insts =
  L.nub $ M.catMaybes [evtChan evt | i <- insts, evt <- trace i]

-- The node orderings form an acyclic order if there are no cycles.
-- Use depth first search to detect cycles.  A graph with no node with
-- an indegree of zero is cyclic and must not be checked with depth
-- first search.
acyclicOrder :: Preskel -> Bool
acyclicOrder k =
    all (not . backEdge numbering) edges
    where
      edges = graphEdges (strands k)
      -- The starting set contains the last node in every strand
      start = map (last . nodes) (strands k)
      -- Remove nodes that have non-zero indegree
      start' = foldl (flip L.delete) start (map fst edges)
      numbering = dfs preds start'

-- Variables in this preskeleton, excluding ones in roles, and ones
-- that only occur in a cause.
kvars :: Preskel -> [Term]
kvars k =
    instVars (insts k)

-- Ensure each role unique origination assumption mapped by an
-- instance originates in the instance's strand.
roleOrigCheck :: Preskel -> Bool
roleOrigCheck k =
    all strandRoleOrig (strands k) -- Check each strand
    where
      strandRoleOrig strand =   -- Check each role unique used in strand
          all (uniqRoleOrig strand) $ ruorig $ role $ inst strand
      uniqRoleOrig strand (ru, pos)
          | pos < height (inst strand) =
              case lookup (instantiate (env $ inst strand) ru) (korig k) of
                Nothing -> True     -- role term not mapped
                Just ns -> any (\(s, i)-> sid strand == s && i == pos) ns
          | otherwise = True

-- Ensure each role unique generation assumption mapped by an
-- instance generates in the instance's strand.
roleGenCheck :: Preskel -> Bool
roleGenCheck k =
    all strandRoleGen (strands k) -- Check each strand
    where
      strandRoleGen strand =   -- Check each role ugen used in strand
          all (uniqRoleGen strand) (filter nonNum (rugen $ role $ inst strand))
      uniqRoleGen strand (ru, pos)
          | pos < height (inst strand) =
              case lookup (instantiate (env $ inst strand) ru) (kugen k) of
                Nothing -> True     -- role term not mapped
                Just ns -> any (\(s, i)-> sid strand == s && i == pos) ns
          | otherwise = True
      nonNum (u, _) = not (isNum u)

-- Channel functions
confCm :: Preskel -> ChMsg -> Bool
confCm k e =
  case cmChan e of
    Just ch -> elem ch (kconf k) || isLocn ch
    Nothing -> False

authCm :: Preskel -> ChMsg -> Bool
authCm k e =
  case cmChan e of
    Just ch -> elem ch (kauth k) ||
               (isLocn ch &&
                (let t = (cmTerm e) in
                 elem t (kgenSt k) ||
                 (isLocnMsg t &&
                  elem (locnMsgPayload t) (kgenSt k))))
    Nothing -> False

-- Isomorphism Check

-- Are two skeletons equivalent?  Two skeletons are equivalent if they
-- are isomorphic.  A key efficiency requirement in the implementation
-- of the cryptograhic protocol shapes analysis algorithm is to ensure
-- only one member of each equivalence class of skeletons is analyzed,
-- and the results of that analysis is immediately used for all other
-- members of the equivalence class.

-- To meet this requirement, a list of skeletons that have been seen
-- is maintained.  Before a skeleton is put on a to do list for
-- analysis, it is checked to see if it is isomorphic to one already
-- seen.  If so, the results of the analysis for the isomorphic
-- skeleton is used instead of putting the skeleton on the to do list.

-- Once a skeleton has been printed, the only reason for saving it is
-- for isomorphism checking.  The isomorphism check is performed
-- frequently, so an specialized data structure is used.  The gist of
-- a skeleton is all that is needed for the test for equivalence.

data Gist = Gist
    { ggen :: Gen,
      gtraces :: [(Int, Trace)],
      gorderings :: [Pair],
      gnon :: [Term],    -- A list of non-originating terms
      gpnon :: [Term],   -- A list of penetrator non-originating terms
      gunique :: [Term], -- A list of uniquely-originating terms
      guniqgen :: [Term], -- A list of uniquely-generated terms
      gabsent :: [(Term, Term)], -- A list of absent terms
      ggenSt :: [Term],  -- A list of terms for generated states
      gfacts :: [Fact],  -- A list of facts
      gfvars :: [Term],  -- Fact vars not in instances
      nvars :: !Int,     -- Number of variables
      ntraces :: !Int,   -- Number of traces
      briefs :: [(Int, Int)],   -- Multiset of trace briefs
      norderings :: !Int,       -- Number of orderings
      nnon :: !Int,      -- Number of non-originating terms
      npnon :: !Int,     -- Number of penetrator non-originating terms
      nunique :: !Int,   -- Number of uniquely-originating terms
      nuniqgen :: !Int,  -- Number of uniquely-generating terms
      nabsent :: !Int,   -- Number of absent terms
      ngenSt :: !Int,    -- Number of generated states
      nfacts :: !Int,    -- Number of facts
      nfvars :: !Int }   -- Number of fact vars not in instances
    deriving Show

mkGist :: Preskel -> Gist
mkGist k =
    Gist { ggen = gen k,
           gtraces = gtraces,
           gorderings = gorderings,
           gnon = gnon,
           gpnon = gpnon,
           gunique = gunique,
           guniqgen = guniqgen,
           gabsent = gabsent,
           ggenSt = ggenSt,
           gfacts = gfacts,
           gfvars = gfvars,
           nvars = length (kvars k),
           ntraces = length gtraces,
           briefs = multiset (map fst gtraces),
           norderings = length gorderings,
           nnon = length gnon,
           npnon = length gpnon,
           nunique = length gunique,
           nuniqgen = length guniqgen,
           nabsent = length gabsent,
           ngenSt  = length ggenSt,
           nfacts = length gfacts,
           nfvars = length gfvars }
    where
      gtraces = map f (insts k)
      -- Old: f i = (height i, trace i)
      f i =
        (brief c, c)
        where c = trace i
      gorderings = orderings k
      gnon = knon k
      gpnon = kpnon k
      gunique = kunique k
      guniqgen = kuniqgen k
      gabsent = kabsent k
      ggenSt = kgenSt k
      gfacts = kfacts k
      gfvars = kfvars k

-- Summarize a trace so that two traces don't match unless they have
-- the same number.  The summary used to be the height of the trace.
brief :: Trace -> Int
brief [] = 0
brief (In _ : c) = 1 + 3 * brief c
brief (Out _ : c) = 2 + 3 * brief c

-- Convert a list of integers into a sorted multiset representation.
-- The output is a list of pairs, (i, n). Integer n gives the
-- multiplity of integer i in the input list.  List is sorted based on
-- the first element in each pair.
multiset :: [Int] -> [(Int, Int)]
multiset brf =
  L.foldl insert [] brf
  where
    insert [] b = [(b, 1)]
    insert ((k, n) : brf) b
      | k == b = (k, n + 1) : brf
      | k > b = (b, 1) : (k, n) : brf
      | otherwise = (k, n) : insert brf b

-- Test to see if two preskeletons are isomorphic

-- First, ensure the two preskeletons have:
-- 1. The same number of variables
-- 2. The same number of strands with the same brief
-- 3. The same number of node orderings
-- 4. The same number of terms in knon and kunique
-- 5. The same number of facts
-- 6. The same number of variables in facts but not in instances

-- Next compute the plausible permutations and substitutions.

-- Next, for each permutation of the strands, eliminate the ones that
-- map a strand to another of a different length, and don't cause the
-- node orderings to be equal.

-- For permutations that meet the previous conditions, see if there is
-- a renaming that maps every strand trace in one preskeleton into the
-- appropriate one in the other preskeleton.  Finally, check to see if
-- the renaming works in the nr and ur terms.

isomorphic :: Gist -> Gist -> Bool
isomorphic g g' =
    sameSkyline g g' &&
    any (tryPerm g g') (permutations g g')

sameSkyline :: Gist -> Gist -> Bool
sameSkyline g g' =
    -- nvars g == nvars g' &&      -- Doesn't work for Diffie-Hellman
    ntraces g == ntraces g' &&
    briefs g == briefs g' &&
    norderings g == norderings g' &&
    nnon g == nnon g' &&
    npnon g == npnon g' &&
    nunique g == nunique g' &&
    nuniqgen g == nuniqgen g' &&
    nabsent g == nabsent g' &&
    ngenSt g == ngenSt g' &&
    nfacts g == nfacts g' &&
    nfvars g == nfvars g'

-- For thinning.  Ensure point-of-view is preserved.
probIsomorphic :: Preskel -> Preskel -> Bool
probIsomorphic k k' =
    sameSkyline g g' &&
    any (tryPermProb g g' pr pr') (permutations g g')
    where
      g = gist k
      g' = gist k'
      pr = prob k
      pr' = prob k'

-- Extend a permutation while extending a substitution
-- Extend by matching later strands first
permutations :: Gist -> Gist -> [((Gen, Env), (Gen, Env), [Sid])]
permutations g g' =
    map rev $ perms (gg, emptyEnv)
                    (gg, emptyEnv)
                    (reverse $ gtraces g)
                    (reverse $ nats $ ntraces g)
    where
      gg = gmerge (ggen g) (ggen g')
      perms env renv [] [] = [(env, renv, [])]
      perms env renv ((h, c):hcs) xs =
          [ (env'', renv'', x:ys) |
            x <- xs,
            let (h', c') = gtraces g' !! x,
            h == h',
            env' <- jibeTraces c c' env,
            renv' <- jibeTraces c' c renv,
            (env'', renv'', ys) <- perms env' renv' hcs (L.delete x xs) ]
      perms _ _ _ _ = error "Strand.permutations: lists not same length"
      rev (env, renv, xs) = (env, renv, reverse xs)

-- Length of matched traces must agree.
jibeTraces :: Trace -> Trace -> (Gen, Env) -> [(Gen, Env)]
jibeTraces [] [] ge = [ge]
jibeTraces (In t : c) (In t' : c') ge =
    do
      env <- cmMatch t t' ge
      jibeTraces c c' env
jibeTraces (Out t : c) (Out t' : c') ge =
    do
      env <- cmMatch t t' ge
      jibeTraces c c' env
jibeTraces _ _ _ = []

-- Extend a fact permutation while extending a substitution
fperms :: Gist -> Gist -> (Gen, Env) -> (Gen, Env) ->
          [((Gen, Env), (Gen, Env), [Int])]
fperms g g' env renv =
  perms env renv (gfvars g) (nats $ nfvars g)
  where
    perms env renv [] [] = [(env, renv, [])]
    perms env renv (t:ts) xs =
          [ (env'', renv'', x:ys) |
            x <- xs,
            let t' = gfvars g' !! x,
            env' <- match t t' env,
            renv' <- match t' t renv,
            (env'', renv'', ys) <- perms env' renv' ts (L.delete x xs) ]
    perms _ _ _ _ = error "Strand.fperms: lists not same length"

{-
-- Here is the permutation algorithm used

permutations :: Int -> [[Int]]
permutations n =
    perms (nats n)
    where
      perms []  = [[]]
      perms xs = [ x:ys | x <- xs, ys <- perms (L.delete x xs) ]

-- Here is the usual algorithm

-- Returns a list of all the permutations of the natural numbers less
-- that the argument.  The identity permutation is the first one in
-- the returned list.  The code is based on a function in Haskell 1.3.
permutations :: Int -> [[Int]]
permutations n =
    perms (nats n)
    where
      perms [] = [[]]
      perms (x:xs) = [zs | ys <- perms xs, zs <- interleave x ys]
      interleave x [] = [[x]]
      interleave x (y:ys) = (x:y:ys) : map (y:) (interleave x ys)
-}

tryPerm :: Gist -> Gist -> ((Gen, Env), (Gen, Env), [Sid]) -> Bool
tryPerm g g' (env, renv, perm) =
    checkOrigs g g' env &&
    checkOrigs g' g renv &&
    checkGenSt g g' env &&
    checkGenSt g' g renv &&
    any (tryFacts g g' perm (invperm perm)) (fperms g g' env renv) &&
    containsMapped (permutePair perm) (gorderings g') (gorderings g)

tryPermProb :: Gist -> Gist -> [Sid] -> [Sid] ->
               ((Gen, Env), (Gen, Env), [Sid]) -> Bool
tryPermProb g g' prob prob' (env, renv, perm) =
    all (\n -> perm !! (prob !! n) == prob' !! n) [0..((length prob)-1)] &&
    tryPerm g g' (env, renv, perm)

invperm :: [Int] -> [Int]
invperm p = map snd (L.sortOn fst (zip p [0..]))

-- containsMapped f xs ys is true when list xs contains each element
-- in ys after being mapped with function f.
containsMapped :: Eq a => (a -> a) -> [a] -> [a] -> Bool
containsMapped f xs ys =
    all (flip elem xs) (map f ys)

permutePair :: [Sid] -> Pair -> Pair
permutePair perm (n, n') = (permuteNode perm n, permuteNode perm n')

permuteNode :: [Sid] -> Node -> Node
permuteNode perm (strand, pos) = (perm !! strand, pos)

tryFacts :: Gist -> Gist -> [Sid] -> [Sid] ->
            ((Gen, Env), (Gen, Env), a) -> Bool
tryFacts g g' perm invperm (env, renv, _) =
  checkFacts g g' env perm &&
  checkFacts g' g renv invperm

checkFacts :: Gist -> Gist -> (Gen, Env) -> [Sid] -> Bool
checkFacts g g' (_, e) perm =
  all f (gfacts g)
  where
    f fact = elem (instUpdateFact e (perm !!) fact) (gfacts g')

checkOrigs :: Gist -> Gist -> (Gen, Env) -> Bool
checkOrigs g g' env =
    not (null
         [ env''''' |
           env' <- checkOrig env (gnon g) (gnon g'),
           env'' <- checkOrig env' (gpnon g) (gpnon g'),
           env''' <- checkOrig env'' (gunique g) (gunique g'),
           env'''' <- checkOrig env''' (guniqgen g) (guniqgen g'),
           env''''' <- checkAbs env'''' (gabsent g) (gabsent g')])

-- Try all permutations as done above
checkOrig :: (Gen, Env) -> [Term] -> [Term] -> [(Gen, Env)]
checkOrig env [] [] = [env]
checkOrig env (t:ts) ts' =
    do
      t' <- ts'
      env' <- match t t' env
      checkOrig env' ts (L.delete t' ts')
checkOrig _ _ _ = error "Strand.checkOrig: lists not same length"

-- Try all permutations as done above
checkAbs :: (Gen, Env) -> [(Term, Term)] -> [(Term, Term)] -> [(Gen, Env)]
checkAbs env [] [] = [env]
checkAbs env ((t1,t2):ts) ts' =
    do
      (t1', t2') <- ts'
      env <- match t1 t1' env
      env <- match t2 t2' env
      checkAbs env ts (L.delete (t1', t2') ts')
checkAbs _ _ _ = error "Strand.checkAbs: lists not same length"

checkGenSt :: Gist -> Gist -> (Gen, Env) -> Bool
checkGenSt g g' env =
    let genStVs = (ggenSt g) in
    let genStVs' = (ggenSt g') in
    let (_, e) = env in
    all (\gs -> (instantiate e gs) `elem` genStVs') genStVs

gist :: Preskel -> Gist
-- gist = mkGist
gist = kgist

-- Preskeleton Reduction System (PRS)

-- The PRS reduces a preskeleton to a list of skeletons.  Along the way,
-- it applies the associated homomorphism to a node and computes a
-- substitution.  Thus if skel (k, n, empty) = [(k', n', sigma)], then
-- phi,sigma is a homomorphism from k to k', n' = phi(n).

type PRS = (Preskel,            -- Parent
            Preskel,            -- Potential cohort member
            Node,               -- Image of test node in member
            [Sid],              -- Strand map part of homomorphism
            Subst)              -- Substition part of homomorphism

-- Extract the protential cohort member from a PRS.
skel :: PRS -> Preskel
skel (_, k, _, _, _) = k

-- Returns the preskeletons that result from applying a substitution.
-- If validate is True, preskeletons that fail to preserve the nodes
-- at which each maybe uniquely originating term originates are
-- filtered out.

ksubst :: PRS -> (Gen, Subst) -> [PRS]
ksubst (k0, k, n, phi, hsubst) (gen, subst) =
    do
      (gen', insts') <- foldMapM (substInst subst) gen (insts k)
      let non' = map (substitute subst) (knon k)
      let pnon' = map (substitute subst) (kpnon k)
      let unique' = map (substitute subst) (kunique k)
      let uniqgen' = map (substitute subst) (kuniqgen k)
      let absent' = map (pairApp $ substitute subst) (kabsent k)
      let genStV' = map (substitute subst) (kgenSt k)
      let conf' = map (substitute subst) (kconf k)
      let auth' = map (substitute subst) (kauth k)
      let facts' = map (substFact subst) (kfacts k)
      let operation' = substOper subst (operation k)
      let k' = newPreskel gen' (shared k) insts'
               (orderings k) non' pnon' unique' uniqgen'
               absent' (kprecur k) genStV' conf' auth' facts'
               (kpriority k) operation' (krules k) (pprob k) (prob k) (pov k)
      k'' <- wellFormedPreskel $ soothePreskel k'
      return (k0, k'', n, phi, compose subst hsubst)

pairApp :: (a -> b) -> (a, a) -> (b, b)
pairApp f (x, y) = (f x, f y)

-- Monad version of mapAccumR
foldMapM :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
foldMapM _ acc [] = return (acc, [])
foldMapM f acc (x:xs) =
    do
      (acc', xs') <- foldMapM f acc xs
      (acc'', x') <- f acc' x
      return (acc'', x':xs')

substInst :: Subst -> Gen -> Instance -> [(Gen, Instance)]
substInst subst gen i =
    bldInstance (role i) (map (evtMap $ substitute subst) (trace i)) gen

substOper :: Subst -> Operation -> Operation
substOper _ New = New
substOper subst (Contracted s cause) =
    Contracted (compose subst s) (substCause subst cause)
substOper _ m@(Displaced _ _ _ _ _) = m
substOper subst (AddedStrand role height cause) =
    AddedStrand role height (substCause subst cause)
substOper subst (AddedListener t cause) =
    AddedListener (substitute subst t) (substCause subst cause)
substOper subst (AddedAbsence t1 t2 cause) =
    AddedAbsence (substitute subst t1) (substitute subst t2) (substCause subst cause)
substOper _ m@(Generalized _) = m
substOper _ m@(Collapsed _ _) = m

substCause :: Subst -> Cause -> Cause
substCause subst (Cause dir n t escape) =
    Cause dir n (cmtSubstitute subst t) (S.map (cmtSubstitute subst) escape)

-- A compression (s is to be eliminated)
compress :: Bool -> PRS -> Sid -> Sid -> [PRS]
compress validate (k0, k, n, phi, hsubst) s s' =
    do
      let perm = updatePerm s s' (strandids k)
      orderings' <- normalizeOrderings validate
                    (permuteOrderings perm (orderings k))
      let k' =
              newPreskel
              (gen k)
              (shared k)
              (deleteNth s (insts k))
              orderings'
              (knon k)
              (kpnon k)
              (kunique k)
              (kuniqgen k)
              (kabsent k)
              (map (permuteNode perm) (kprecur k))
              (kgenSt k)
              (kconf k)
              (kauth k)
              (map (updateFact $ updateStrand s s') (kfacts k))
              (updatePriority perm (kpriority k))
              (operation k)
              (krules k)
              (pprob k)
              (updateProb perm (prob k))
              (pov k)
      k'' <- wellFormedPreskel k'
      return (k0, k'', permuteNode perm n, map (perm !!) phi, hsubst)

permuteOrderings :: [Sid] -> [Pair] -> [Pair]
permuteOrderings perm orderings = map (permutePair perm) orderings

updatePerm :: Int -> Int -> [Sid] -> [Sid]
updatePerm old new perm =
    map (updateStrand old new) perm

-- Old is to be eliminated and merged into new
updateStrand :: Int -> Int -> Sid -> Sid
updateStrand old new i =
    let j = if old == i then new else i in
    if j > old then j - 1 else j

updateNode :: Int -> Int -> Node -> Node
updateNode old new (s, i) =
    (updateStrand old new s, i)

-- Eliminates implied intrastrand orderings and fails if it finds a
-- reverse intrastrand ordering when flag is true.
normalizeOrderings :: Bool -> [Pair] -> [[Pair]]
normalizeOrderings True orderings =
    loop [] orderings
    where
      loop acc [] = [acc]
      loop acc (p@((s0, i0), (s1, i1)) : ps)
          | s0 /= s1 = loop (p : acc) ps
          | i0 < i1 = loop acc ps
          | otherwise = []
normalizeOrderings False orderings =
    [filter (\ ((s0, _), (s1, _)) -> s0 /= s1) orderings]

updateProb :: [Sid] -> [Sid] -> [Sid]
updateProb mapping prob =
    map (mapping !!) prob

updatePriority :: [Sid] -> [(Node, Int)] -> [(Node, Int)]
updatePriority mapping kpriority =
    map (\(n, i) -> (permuteNode mapping n, i)) kpriority

-- Purge strand s.  Used by thinning.  Expects s and s' to be isomorphic.
purge :: PRS -> Sid -> Sid -> [PRS]
purge (k0, k, n, phi, hsubst) s s' =
    do
      let perm = updatePerm s s' (strandids k)
      orderings' <- normalizeOrderings False
                    (permuteOrderings perm
                     (forward s (orderings k)))
      let k' =
              newPreskel
              (gen k)
              (shared k)
              (deleteNth s (insts k))
              orderings'
              (knon k)
              (kpnon k)
              (kunique k)
              (kuniqgen k)
              (kabsent k)
              (map (permuteNode perm) (kprecur k))
              (kgenSt k)
              (kconf k)
              (kauth k)
              (map (updateFact $ updateStrand s s')
                       (deleteStrandFacts s (kfacts k)))
              (updatePriority perm (kpriority k))
              (operation k)
              (krules k)
              (pprob k)
              (updateProb perm (prob k))
              (pov k)
      k'' <- wellFormedPreskel $ soothePreskel k'
      return (k0, k'', permuteNode perm n, map (perm !!) phi, hsubst)

-- Forward orderings from strand s
forward :: Sid -> [Pair] -> [Pair]
forward s orderings =
    concatMap f orderings
    where
      f p@((s0, i0), (s1, i1))
          | s0 == s = [((s2, i2), (s1, i1)) | -- Forward here
                       ((s2, i2), (s3, i3)) <- orderings,
                       s3 == s0 && i0 >= i3]
          | s1 == s = []        -- Dump edges to strand s
          | otherwise = [p]     -- Pass thru other edges

-- Remove bad origination assumptions, gen-states, and facts
soothePreskel :: Preskel -> Preskel
soothePreskel k =
  newPreskel
  (gen k)
  (shared k)
  (insts k)
  (orderings k)
  (filter varCheck $ knon k)
  (filter varCheck $ kpnon k)
  (filter carriedCheck $ kunique k)
  (filter varCheck $ kuniqgen k)
  (filter absentCheck $ kabsent k)
  (kprecur k)
  (filter genStCheck $ kgenSt k)
  (filter chanCheck $ kconf k)
  (filter chanCheck $ kauth k)
  (kfacts k)
  (kpriority k)
  (operation k)
  (krules k)
  (pprob k)
  (prob k)
  (pov k)
  where
    vs = kvars k
    terms = kterms k
    f b t = b && t `elem` vs
    varCheck t = varSubset [t] terms
    carriedCheck t = any (carriedBy t) terms
    genStCheck t = foldVars f True t
    chanCheck t = varSubset [t] $ kchans k
    absentCheck (x, y) = varSubset [x, y] $ kvars k

-- This is the starting point of the Preskeleton Reduction System

skeletonize :: Bool -> PRS -> [PRS]
skeletonize thin prs =
  do
    prs' <- enforceAbsence prs
    case origGenChecks prs' of
      True -> []
      False -> enrich thin prs'

-- Compute the substitutions that satisfy the absence assumptions and
-- apply them to the skeleton.
enforceAbsence :: PRS -> [PRS]
enforceAbsence prs@(_, k, _, _, _)
  | null (kabsent k) = [prs]
enforceAbsence prs@(_, k, _, _, _) =
  do
    s <- foldl f [(gen k, emptySubst)] (kabsent k)
    ksubst prs s
  where
    f ss ts =
      do
        s <- ss
        absentSubst s ts

-- Determine if a given PRS has a multiple origination of a
-- non-numeric fresh value.  Also when a value is both uniq
-- orig and uniq gen, check to see if they start on different strands.
-- When a value is uniq gen and a *different* strand receives it in
-- non-carried position and then transmits in carried position, that's
-- also a problem.  If k is an asymmetric key, its inverse is
-- generated at the same node at which it is uniquely generated.

origGenChecks :: PRS -> Bool
origGenChecks prs =
  any (\(_, l) -> length l > 1) (korig (skel prs)) ||
  any (\(_, l) -> length l > 1) (kugen (skel prs)) ||
  origUgenDiffStrand (korig (skel prs)) (ugensPlusInverses (skel prs)) ||
  not(ugenGoodOrig (skel prs))

-- When a value is both uniq orig and uniq gen, check to see if they
-- start on different strands.
origUgenDiffStrand :: [(Term, [Node])] -> [(Term, [Node])] -> Bool
origUgenDiffStrand _ [] = False
origUgenDiffStrand orig ((t, ns) : ugen) =
  (case lookup t orig of
     Nothing -> origUgenDiffStrand orig ugen
     Just ns' -> any (f ns') ns || origUgenDiffStrand orig ugen)
  ||
  (maybe False
   (\t' -> case lookup t' orig of
             Nothing -> False
             Just ns' -> any (f ns') ns)
   $ invertKey t)
    where
      f ns' (s, _) = any (\(s', _) -> s /= s') ns'

-- Hulling or Ensuring Unique Origination
hull :: Bool -> PRS -> [PRS]
hull thin prs =
    loop (korig (skel prs) ++ kugen (skel prs))
    where
      -- No uniques originate on more than one strand
      loop [] = enrich thin prs
      -- Found a pair that needs hulling
      loop ((_, (s, _) : (s', _) : _) : _) =
        do
          (s'', s''', subst) <- unifyStrands (skel prs) s s'
          prs <- ksubst prs subst
          prs' <- compress False prs s'' s'''
          hull thin prs'
      loop(_ : orig) = loop orig

-- Order Enrichment

-- Adds orderings so that a skeleton respects origination.

enrich :: Bool -> PRS -> [PRS]
enrich _ prs | origGenChecks prs = []
enrich thin (k0, k, n, phi, hsubst) =
    let o = foldl (addUniqOrigOrderings k) (orderings k) (kunique k) in
    let o' = foldl (addUniqGenOrderings k) o (kuniqgen k) in
    if length o' == length (orderings k) then
        maybeThin thin (k0, k, n, phi, hsubst) -- Nothing to add
    else
        do
          let k' =
                  newPreskel
                  (gen k)
                  (shared k)
                  (insts k)
                  o'
                  (knon k)
                  (kpnon k)
                  (kunique k)
                  (kuniqgen k)
                  (kabsent k)
                  (kprecur k)
                  (kgenSt k)
                  (kconf k)
                  (kauth k)
                  (kfacts k)
                  (kpriority k)
                  (operation k)
                  (krules k)
                  (pprob k)
                  (prob k)
                  (pov k)
          k'' <- wellFormedPreskel k'
          maybeThin thin (k0, k'', n, phi, hsubst)

maybeThin :: Bool -> PRS -> [PRS]
maybeThin _ prs | usePruning = prune prs
maybeThin True prs = thin prs
maybeThin False prs = reduce prs

origNode :: Preskel -> Term -> Maybe Node
origNode k t =
    case lookup t (korig k) of
      Nothing -> error "Strand.origNode: term not in kunique"
      Just [] -> Nothing
      Just [n] -> Just n
      Just _ -> error "Strand.origNode: not a hulled skeleton"

addUniqOrigOrderings :: Preskel -> [Pair] -> Term -> [Pair]
addUniqOrigOrderings k orderings t =
    case origNode k t of
      Nothing -> orderings
      Just n@(s, _) ->
          foldl f orderings (L.delete s (strandids k))
          where
            f orderings s =
                -- JDG:  Was gainedPos:  usedPos seemed more correct
                -- before further checking...
                case gainedPos t (trace (strandInst k s)) of
                  Nothing -> orderings
                  Just pos -> adjoin (n, (s, pos)) orderings

genNode :: Preskel -> Term -> Maybe Node
genNode k t =
    case lookup t (kugen k) of
      Nothing -> error "Strand.genNode: term not in kuniqgen"
      Just [] -> Nothing
      Just [n] -> Just n
      Just _ -> error "Strand.genNode: not a hulled skeleton"

addUniqGenOrderings :: Preskel -> [Pair] -> Term -> [Pair]
addUniqGenOrderings k orderings t =
    case genNode k t of
      Nothing -> orderings
      Just n@(s, _) ->
          foldl f orderings (L.delete s (strandids k))
          where
            f orderings s =
                -- JDG:  Was genGainedPos:  usedPos seems more correct
                case usedPos t (trace (strandInst k s)) of
                  Nothing -> orderings
                  Just pos -> adjoin (n, (s, pos)) orderings

matchTraces :: Trace -> Trace -> (Gen, Env) -> [(Gen, Env)]
matchTraces [] _ env = [env]    -- Pattern can be shorter
matchTraces (In t : c) (In t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces (Out t : c) (Out t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces _ _ _ = []

-- Thinning

thin :: PRS -> [PRS]
thin prs =
  do
    prs <- reduce prs
    thinStrands prs [] $ reverse ss
    where                       -- Remove strands in image of POV
      ss = filter (\s -> notElem s (prob $ skel prs)) (strandids $ skel prs)

-- Takes a skeleton, a list of pairs of strands that matched, and a
-- list of strands yet to be analyzed, and produces the result of
-- skeletonization.  It first tries single pair thinning, and during
-- that process collects potential multistrand thinning pairs.  Once
-- there are no more unanalyzed strands, it tries multistrand
-- thinning.
thinStrands :: PRS -> [(Sid, Sid)] -> [Sid] -> [PRS]
thinStrands prs ps [] =         -- All strands analyzied
    case multiPairs ps of       -- Generate multipairs
      [] -> reduce prs
      mps -> thinMany prs mps   -- Try multistrand thinning
thinStrands prs ps (s:ss) =
  thinStrandPairs prs ps s ss ss

-- This loop tries pairs of strands.  Takes a skeleton, a list of
-- pairs of strands that matched but did not thin, a strand to be
-- eliminated, a list of strands to be used in the outer loop
-- (thinStrands), and a list of strands to be considered for matching,
-- and produces the result of skeletonization.
thinStrandPairs :: PRS -> [(Sid, Sid)] -> Sid -> [Sid] -> [Sid] -> [PRS]
thinStrandPairs prs ps _ ss [] =
  thinStrands prs ps ss
thinStrandPairs prs ps s ss (s':ss') =
  case thinStrand prs s s' of
    -- Try next pair, there was no match
    Nothing -> thinStrandPairs prs ps s ss ss'
    -- Try next pair, there was a match so save this pair
    Just [] -> thinStrandPairs prs ((s, s'):ps) s ss ss'
    Just prss ->                -- Success at single strand thinning
      do
        prs <- prss
        thin prs                -- Restart from the beginning

-- Try thinning s with s'.  If there was no match, return Nothing,
-- else return Just the list of results.
thinStrand :: PRS -> Sid -> Sid -> Maybe [PRS]
thinStrand prs s s' =
    let k = skel prs in
    case thinStrandMatch k s s' of
      False -> Nothing
      True ->
        Just [ prs' | prs' <- purge prs s s',
                      prs'' <- purge prs s' s,
                      probIsomorphic (skel prs') (skel prs'')]

-- See if two strands match.
thinStrandMatch :: Preskel -> Sid -> Sid -> Bool
thinStrandMatch k s s' =
  height i == height i'
  && not (null $ matchTraces (trace i) (trace i') env)
  && not (null $ matchTraces (trace i') (trace i) env)
  where
    i = strandInst k s
    i' = strandInst k s'
    env = (gen k, emptyEnv)

-- Multistrand thinning

-- Generate all candidate pairings
multiPairs :: [(Sid, Sid)] ->  [[(Sid, Sid)]]
multiPairs _ | useSingleStrandThinning = []
multiPairs ps = filter atLeastTwo $ thinOne ps

-- List is of length at least two.
atLeastTwo :: [a] -> Bool
atLeastTwo (_:_:_) = True
atLeastTwo _ = False

thinOne :: [(Sid, Sid)] -> [[(Sid, Sid)]]
thinOne [] = []
thinOne (p:ps) =
    thinTwo p ps ++ thinOne ps

-- Construct possible pairs that include (s, s').
thinTwo :: (Sid, Sid) -> [(Sid, Sid)] -> [[(Sid, Sid)]]
thinTwo (s, s') ps =
    [(s, s')] : [(s, s') : ps' | ps' <- thinOne (filter (diff (s, s')) ps)]
    where                       -- filter out pairs with seen strands
      diff (s0, s1) (s2, s3) =
          s0 /= s2 && s0 /= s3 && s1 /= s2 && s1 /= s3

-- Try all multistrand pairings until one succeeds.
thinMany :: PRS -> [[(Sid, Sid)]] -> [PRS]
thinMany prs [] = reduce prs
thinMany prs (ps:mps) =
    case thinManyStrands prs ps of
      [] -> thinMany prs mps
      prss ->                           -- Success
        do
          prs <- prss
          thin prs

thinManyStrands :: PRS -> [(Sid, Sid)] -> [PRS]
thinManyStrands prs ps =
  [ prs' | prs' <- compressMany prs ps,
           prs'' <- compressMany prs (swap ps),
           probIsomorphic (skel prs') (skel prs'')]

compressMany :: PRS -> [(Sid, Sid)] -> [PRS]
compressMany prs [] = [prs]
compressMany prs ((s, s'):ps) =
    do
      prs' <- purge prs s s'
      compressMany prs' (map (updatePairs s s') ps)

swap :: [(a, a)] -> [(a, a)]
swap ps =
    map (\(x, y) -> (y, x)) ps

updatePairs :: Sid -> Sid -> (Sid, Sid) -> (Sid, Sid)
updatePairs old new (s, s') =
    (updateStrand old new s, updateStrand old new s')

-- Redundant Strand Elimination (also known as pruning)

prune :: PRS -> [PRS]
prune prs =
    pruneStrands prs (reverse $ strandids $ skel prs) (strandids $ skel prs)

pruneStrands :: PRS -> [Sid] -> [Sid] -> [PRS]
pruneStrands prs [] _ =
    reduce prs                  -- No redundant strands found
pruneStrands prs (_:ss) [] =
    pruneStrands prs ss (strandids $ skel prs)
pruneStrands prs (s:ss) (s':ss')
    | s == s' = pruneStrands prs (s:ss) ss'
    | otherwise =
        case pruneStrand prs s s' of
          [] -> pruneStrands prs (s:ss) ss'  -- Try next pair
          prss ->                            -- Success
              do
                prs <- prss
                prune prs

-- Strand s is redundant if there is an environment that maps
-- the trace of s into a prefix of the trace of s', but changes
-- no other traces in the preskeleton.
pruneStrand :: PRS -> Sid -> Sid -> [PRS]
pruneStrand prs s s' =
    do
      let k = skel prs
      case elem s (prob k) of
        True -> fail ""   -- Strands s in image of POV skeleton
        False -> return ()
      (g, env) <- matchTraces
                  (trace (strandInst k s))
                  (trace (strandInst k s'))
                  (gen k, emptyEnv)
      let ts = concatMap (tterms . trace) $ deleteNth s $ insts k
      let subst = substitution env
      case disjointDom subst ts of
        True -> return ()
        False -> fail ""
      case origCheck k env of
        True -> return ()
        False -> fail ""
      -- If performing strong pruning, drop inbound edges to strand s.
      let k' = if useStrongPruning then dropInbnd k s else k
      let prs' = if useStrongPruning then setSkel prs k' else prs
      case all (precedesCheck k' s s') (edges k') of
        True -> return ()
        False -> fail ""
      prs' <- ksubst prs' (g, subst)
      compress True prs' s s'

-- Make sure a substitution does not take a unique out of the set of
-- uniques, and the same for uniq gens, nons, and pnons.
origCheck :: Preskel -> Env -> Bool
origCheck k env =
    check (kunique k) && check (kuniqgen k) &&
    check (knon k) && check (kpnon k)
    where
      check orig =
          all (pred orig) orig
      pred set item =
          elem (instantiate env item) set

-- Ensure that if (s, p) precedes (s", p"), then (s', p) precedes (s", p")
-- and if (s", p") precedes (s, p), then (s", p") precedes (s', p)
precedesCheck :: Preskel -> Sid -> Sid -> Edge -> Bool
precedesCheck k s s' (gn0, gn1)
    | s == sid (strand gn0) = graphPrecedes (vertex k (s', pos gn0)) gn1
    | s == sid (strand gn1) = graphPrecedes gn0 (vertex k (s', pos gn1))
    | otherwise = True

dropInbnd :: Preskel -> Sid -> Preskel
dropInbnd k s =
  newPreskel (gen k) (shared k) (insts k) orderings'
  (knon k) (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
  (kgenSt k) (kconf k) (kauth k) (kfacts k)
  (kpriority k) (operation k) (krules k) (pprob k) (prob k) (pov k)
  where
    orderings' = forward s $ orderings k

setSkel :: PRS -> Preskel -> PRS
setSkel (k0, _, n, phi, hsubst) k = (k0, k, n, phi, hsubst)

-- Transitive Reduction

-- An edge is essential if its removal eliminates all paths from its
-- source to its destination.  This function removes all non-essential
-- edges from the ordering relation.

reduce :: PRS -> [PRS]
reduce (k0, k, n, phi, hsubst) =
    let o = map graphPair (graphReduce (edges k)) in
    if length o == length (orderings k) then
        return (k0, k, n, phi, hsubst) -- Nothing to take away
    else
        do
          let k' =
                  newPreskel
                  (gen k)
                  (shared k)
                  (insts k)
                  o
                  (knon k)
                  (kpnon k)
                  (kunique k)
                  (kuniqgen k)
                  (kabsent k)
                  (kprecur k)
                  (kgenSt k)
                  (kconf k)
                  (kauth k)
                  (kfacts k)
                  (kpriority k)
                  (operation k)
                  (krules k)
                  (pprob k)
                  (prob k)
                  (pov k)
          k'' <- wellFormedPreskel k'
          return (k0, k'', n, phi, hsubst)

-- Answers for cohorts
type Ans = (Preskel, Node, [Sid], Subst)

ans :: PRS -> Ans
ans (_, k, n, phi, subst) = (k, n, phi, subst)

-- Homomorphism Filter

homomorphismFilter :: PRS -> [Ans]
homomorphismFilter prs@(k0, k, _, phi, subst)
    | validateMappingSubst k0 phi subst k = [ans prs]
    | otherwise = []

-- Ensure origination and generation nodes are preserved as required
-- to be a homomorphism
validateMappingSubst :: Preskel -> [Sid] -> Subst -> Preskel -> Bool
validateMappingSubst k phi subst k' =
    useNoOrigPreservation ||
    all checkOrig (korig k) &&  all checkGen (kugen k)
    where
      checkOrig (u, ns) =
          case lookup (substitute subst u) (korig k') of
            Nothing -> False
            Just ns' -> all (flip elem ns') (map (permuteNode phi) ns)
      checkGen (u, ns) =
          case lookup (substitute subst u) (kugen k') of
            Nothing -> False
            Just ns' -> all (flip elem ns') (map (permuteNode phi) ns)

-- Returns the skeleton associated with a preskeleton or nothing when
-- there isn't one.  Manufacture a node and a term, and then drop them
-- afterwards.
toSkeleton :: Bool -> Preskel -> [Preskel]
toSkeleton thin k =
    do
      prs <- hull thin (k, k, (0, 0), strandids k, emptySubst)
      (k', _, _, _) <- homomorphismFilter prs
      return k'

-- Contraction

contract :: Preskel -> Node -> Cause -> (Gen, Subst) -> [Ans]
contract k n cause subst =
    do
      prs <- ksubst (k, k { operation = Contracted emptySubst cause,
                            krules = [] },
                     n, strandids k, emptySubst) subst
      prs' <- skeletonize useThinningWhileSolving prs
      homomorphismFilter prs'

-- Regular Augmentation

-- First argument determines if displacement is used.
augment :: Preskel -> Node -> Cause -> Role ->
           (Gen, Subst) -> Instance -> [Ans]
augment k0 n cause role subst inst =
    do
      prs <- augmentAndDisplace k0 n cause role subst inst
      homomorphismFilter prs

-- Apply a substitution, and then augment and displace.  Augmentations
-- add an instance and one ordered pair.  Displacements add an ordered
-- pair and may add nodes.

augmentAndDisplace :: Preskel -> Node -> Cause -> Role ->
                      (Gen, Subst) -> Instance -> [PRS]
augmentAndDisplace k0 n cause role subst inst =
    do
      prs <- substAndAugment k0 n cause role subst inst
      augDisplace prs ++ skeletonize useThinningWhileSolving prs

-- Apply the substitution and apply augmentation operator.
substAndAugment :: Preskel -> Node -> Cause -> Role ->
                   (Gen, Subst) -> Instance -> [PRS]
substAndAugment k n cause role subst inst =
    do
      let operation' = AddedStrand (rname role) (height inst) cause
      prs <- ksubst (k, k { operation = operation',
                            krules = [] }, n,
                     strandids k, emptySubst) subst
      aug prs inst

-- Apply the augmentation operator by adding an instance and one
-- ordered pair.
aug :: PRS -> Instance -> [PRS]
aug (k0, k, n, phi, hsubst) inst =
    do
      let insts' = (insts k) ++ [inst]
      let pair = ((length (insts k), height inst - 1), n)
      let orderings' = pair : orderings k
      let non' = inheritRnon inst ++ knon k
      let pnon' = inheritRpnon inst ++ kpnon k
      let unique' = inheritRunique inst ++ kunique k
      let uniqgen' = inheritRuniqgen inst ++ kuniqgen k
      let absent' = inheritRabsent inst ++ kabsent k
      let conf' = inheritRconf inst ++ kconf k
      let auth' = inheritRauth inst ++ kauth k
      let k' = newPreskel (gen k) (shared k) insts'
           orderings' non' pnon' unique' uniqgen' absent' (kprecur k)
           (kgenSt k) conf' auth' (kfacts k) (kpriority k)
           (operation k) (krules k) (pprob k) (prob k) (pov k)
      k'' <- wellFormedPreskel k'
      return (k0, k'', n, phi, hsubst)

-- Inherit non-originating atoms if the trace is long enough
inheritRnon :: Instance -> [Term]
inheritRnon i =
    inherit i (rnorig (role i))

-- Inherit penenetrator non-originating atoms if the trace is long enough
inheritRpnon :: Instance -> [Term]
inheritRpnon i =
    inherit i (rpnorig (role i))

-- Inherit uniquely originating atoms if the trace is long enough
inheritRunique :: Instance -> [Term]
inheritRunique i =
    inherit i (ruorig (role i))

-- Inherit uniquely generating atoms if the trace is long enough
inheritRuniqgen :: Instance -> [Term]
inheritRuniqgen i =
    inherit i (rugen (role i))

-- Inherit confidential channels if the trace is long enough
inheritRconf :: Instance -> [Term]
inheritRconf i =
    inherit i (rpconf (role i))

-- Inherit authenticated channels if the trace is long enough
inheritRauth :: Instance -> [Term]
inheritRauth i =
    inherit i (rpauth (role i))

inherit :: Instance -> [(Term, Int)] -> [Term]
inherit i rorigs =
    map (instantiate (env i) . fst) $ filter f rorigs
    where
      f (_, pos) = pos < height i

inheritRabsent :: Instance -> [(Term, Term)]
inheritRabsent i =
    map g abs
    where
      g (x, y, _) = (instantiate (env i) x, instantiate (env i) y)
      abs = filter f (rabs (role i))
      f (_, _, pos) = pos < height i

-- Add all displacements
augDisplace :: PRS -> [PRS]
augDisplace prs =
    do
      let s = nstrands (skel prs) - 1
      s' <- nats s
      augDisplaceStrands prs s s'

-- Try to displace with strand s'
augDisplaceStrands :: PRS -> Sid -> Sid -> [PRS]
augDisplaceStrands (k0, k, n, phi, hsubst) s s' =
    do
      (s, s', subst) <- unifyStrands k s s'
      let op = addedToDisplaced (operation k) s s'
      prs <- ksubst (k0, k { operation = op, krules = [] },
                     n, phi, hsubst) subst
      prs <- compress True prs s s'
      skeletonize useThinningWhileSolving prs

-- See if two strands unify.  They can be of differing heights.  The
-- second strand returned may be longer.
unifyStrands :: Preskel -> Sid -> Sid -> [(Sid, Sid, (Gen, Subst))]
unifyStrands k s s' =
    let i = strandInst k s
        i' = strandInst k s' in
    if height i > height i' then
        unifyStrands k s' s
    else
        do
          (gen', subst) <- unifyTraces (trace i) (trace i') (gen k, emptySubst)
          return (s, s', (gen', subst))

-- Unify traces where the first trace is allowed to be shorter than
-- the second trace.
unifyTraces :: Trace -> Trace -> (Gen, Subst) -> [(Gen, Subst)]
unifyTraces [] _ subst = [subst]
unifyTraces (In t : c) (In t' : c') subst =
    do
      s <- cmUnify t t' subst
      unifyTraces c c' s
unifyTraces (Out t : c) (Out t' : c') subst =
    do
      s <- cmUnify t t' subst
      unifyTraces c c' s
unifyTraces _ _ _ = []

addedToDisplaced :: Operation -> Int -> Int -> Operation
addedToDisplaced (AddedStrand role height cause) s s' =
    Displaced s s' role height cause
addedToDisplaced _ _ _ = error "Strand.addedToDisplaced: Bad operation"

-- Listener Augmentation

addListener :: Preskel -> Node -> Cause -> Term -> [Ans]
addListener k n cause t =
    do
      k'' <- wellFormedPreskel k'
      prs <- skeletonize useThinningWhileSolving
             (k, k'', n, strandids k, emptySubst)
      homomorphismFilter prs
    where
      k' = newPreskel gen' (shared k) insts' orderings' (knon k)
           (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
           (kgenSt k) (kconf k) (kauth k) (kfacts k) (kpriority k)
           (AddedListener t cause) [] (pprob k) (prob k) (pov k)
      (gen', inst) = mkListener (protocol k) (gen k) t
      insts' = insts k ++ [inst]
      pair = ((length (insts k), 1), n)
      orderings' = pair : orderings k

-- Base Listener Augmentation.  Like listener augmentation but adds a
-- base precursor and a precur assertion.

addBaseListener :: Preskel -> Node -> Cause -> Term -> [Ans]
addBaseListener k n cause t =
    case baseRndx t of
      Just ts ->
        do
          x <- ts
          addListener k n cause x
      _ -> formerAddBaseListener k n cause t

formerAddBaseListener :: Preskel -> Node -> Cause -> Term -> [Ans]
formerAddBaseListener k n cause t =
    do
      k'' <- wellFormedPreskel k'
      prs <- skeletonize useThinningWhileSolving
             (k, k'', n, strandids k, emptySubst)
      homomorphismFilter prs
    where
      k' = newPreskel gen'' (shared k) insts' orderings' (knon k)
           (kpnon k) (kunique k) (kuniqgen k) (kabsent k) precur'
           (kgenSt k) (kconf k) (kauth k) (kfacts k) (kpriority k)
           (AddedListener t' cause) [] (pprob k) (prob k) (pov k)
      (gen', t') = basePrecursor (gen k) t
      (gen'', inst) = mkListener (protocol k) gen' t'
      insts' = insts k ++ [inst]
      pair = ((length (insts k), 1), n)
      orderings' = pair : orderings k
      precur' = (length (insts k), 0) : kprecur k

-- addAbsence
addAbsence :: Preskel -> Node -> Cause -> Term -> Term -> [Ans]
addAbsence k n cause x t =
    do
      k'' <- wellFormedPreskel k'
      prs <- skeletonize useThinningWhileSolving
             (k, k'', n, strandids k, emptySubst)
      homomorphismFilter prs
    where                       -- New cause should be added!
      k' = newPreskel (gen k) (shared k) (insts k) (orderings k)
           (knon k) (kpnon k) (kunique k) (kuniqgen k) absent' (kprecur k)
           (kgenSt k) (kconf k) (kauth k) (kfacts k) (kpriority k)
           (AddedAbsence x t cause) (krules k) (pprob k) (prob k) (pov k)
      absent' = (x, t) : kabsent k

-- Homomorphisms

-- Find a substitution that demonstrates the existence of a
-- homomorphism from k to k' using the given strand mapping function.

homomorphism :: Preskel -> Preskel -> [Sid] -> [Env]
homomorphism k k' mapping =
    do
      (_, env) <- findReplacement k k' mapping
      case validateEnv k k' mapping env of
        True -> [env]
        False -> []

{--     filter (validateEnv k k mapping)
               $ map snd
                     $ findReplacement k k' mapping
                     --}

{--  where
         maybeShow x = if (5 == L.length (insts k') &&
                           4 == L.length (insts k))
                       then (z "validateEnv failed"
                             x)
                       else x
                       --}

                            {--
                                ((show (trace ((insts k') !! 0))) ++
                                 " should match pattern " ++
                                 (show (trace ((insts k) !! 0))) ++
                                " mapping " ++ (show mapping))
                            --}

findReplacement :: Preskel -> Preskel -> [Sid] -> [(Gen, Env)]
findReplacement k k' mapping =
    if (L.length mapping) == (L.length (insts k))
    then let v = (let gg = gmerge (gen k) (gen k') in
                  foldM (matchStrand k k' mapping) (gg, emptyEnv) (strandids k))  in
         v
--            if (5 == L.length (insts k') &&
--                4 == L.length (insts k))
--            then
--                z (show (L.length v)) v
--            else v
    else []
        -- error ("Yarg! JDR " ++ (show (L.length mapping)) ++ " vs " ++
        --       (show (L.length (insts k))))

matchStrand :: Preskel -> Preskel -> [Sid] -> (Gen, Env) -> Sid -> [(Gen, Env)]
matchStrand k k' mapping env s =
    matchTraces (trace (strandInst k s)) (trace (strandInst k' s')) env
    where
      s' = mapping !! s

validateEnv :: Preskel -> Preskel -> [Sid] -> Env -> Bool
validateEnv k k' mapping env =
    all (flip elem (knon k')) (map (instantiate env) (knon k)) &&
    all (flip elem (kpnon k')) (map (instantiate env) (kpnon k)) &&
    all (flip elem (kunique k')) (map (instantiate env) (kunique k)) &&
    all (flip elem (kuniqgen k')) (map (instantiate env) (kuniqgen k)) &&
    all (flip elem (kabsent k')) (map (instantiatePair env) (kabsent k)) &&
     --    all (flip elem (kprecur k')) (map (permuteNode mapping) (kprecur k)) &&
    all (flip elem (kfacts k'))
            (map (instUpdateFact env (mapping !!)) (kfacts k)) &&
    all (flip elem (kgenSt k')) (map (instantiate env) (kgenSt k)) &&
    validateEnvOrig k k' mapping env &&
    all (flip elem (tc k')) (permuteOrderings mapping (orderings k))
    where
      instantiatePair env (t1, t2) =
        (instantiate env t1, instantiate env t2)

{-- Degugging apparatus:
      allShowingFailingIndex _ [] = True
      allShowingFailingIndex i (True : rest) = allShowingFailingIndex (i+1) rest
      allShowingFailingIndex i (False : _) =
          if (5 == L.length (insts k') &&
              4 == L.length (insts k))
          then
              z (show i ++ " failed this time")
              False
          else
              False
              --}

validateEnvOrig :: Preskel -> Preskel -> [Sid] -> Env -> Bool
validateEnvOrig k k' mapping env =
    useNoOrigPreservation ||
    all checkOrig (korig k) &&  all checkGen (kugen k)
    where
      checkOrig (u, ns) =
          case lookup (instantiate env u) (korig k') of
            Nothing -> error "Strand.validateEnv: term not in kunique"
            Just ns' -> all (flip elem ns') (map (permuteNode mapping) ns)
      checkGen (u, ns) =
          case lookup (instantiate env u) (kugen k') of
            Nothing -> error "Strand.validateEnv: term not in kuniqgen"
            Just ns' -> all (flip elem ns') (map (permuteNode mapping) ns)

-- Given a realized skeleton k, generate candidates for minimization.
-- A candidate is a preskeleton and a strand mapping from the
-- candidate to k.  The preskeleton need not be well formed, as that
-- test is applied elsewhere.

type Candidate = (Preskel, [Sid])

addIdentity :: Preskel -> Candidate
addIdentity k = (k, strandids k)

separateVariablesLimit :: Int
separateVariablesLimit = 1024

generalize :: Preskel -> [Candidate]
generalize k = deleteTerminal k ++
               deleteNodes k ++
               forgetAssumption k ++
               weakenOrderings k ++
               (if useVariableSeparation
                then take separateVariablesLimit (separateVariables k)
                else [])

-- terminal strand deletion

strandTerminal :: Preskel -> Sid -> Bool
strandTerminal k s =
    not(any (\((s1,_),_) -> s == s1) (orderings k))

strandNonPov :: Preskel -> Sid -> Bool
strandNonPov k s =
    not (elem s (prob k))       -- the members of the mapping *are*
                                -- its range

deleteTerminal :: Preskel -> [Candidate]
deleteTerminal k =
    report v
    where
      v = [(withCoreFacts
            (deleteNodeRest k (gen k) (s, 0)
             (deleteNth s (insts k))
             (deleteOrderings s (tc k))
             (updatePerm s s (prob k))
             (map (updateFact (updateStrand s s))
                      (deleteStrandFacts s $ kfacts k))),
            deleteNth s (strandids k),
            s)
          | s <- [0 .. (L.length (insts k))-1],
                 strandNonPov k s,
                 strandTerminal k s]
      report [] = []
      report ((k', mapping, _) : rest) = (k',mapping) : report rest

 {-- debugging apparatus:
   (zP
           ("dT: strand " ++ (show s) ++ " insts: " ++ (show (L.length (insts k'))) ++
            " prob: " ++ (show (prob k')))
           (k',mapping)) : report rest
           --}

-- Node deletion

{-

delete node n in k

1. if (s, 0) part of prob return Nothing
2. if not initial node, truncate instance of node else delete instance
3. weaken ordering when filtering it (see shortenOrdering)
4. drop nons that aren't mentioned anywhere
5. drop uniques that aren't carried anywhere
6. update prob upon instance deletion
-}

deleteNodes :: Preskel -> [Candidate]
deleteNodes k =
    do
      strand <- strands k
      node <- nodes strand
      cand <- deleteNode k node
      return $ candWithCoreFacts cand

candWithCoreFacts :: Candidate -> Candidate
candWithCoreFacts (k,sids) =
    (withCoreFacts k, sids)

deleteNode :: Preskel -> Vertex -> [(Preskel, [Sid])]
deleteNode k n
    | p == 0 && elem s (prob k) = []
    | p == 0 =
        do
          let mapping = deleteNth s (strandids k)
          let k' = deleteNodeRest k (gen k) (s, p)
                   (deleteNth s (insts k))
                   (deleteOrderings s (tc k))
                   (updatePerm s s (prob k))
                   (map
                     (updateFact (updateStrand s s))
                     (deleteStrandFacts s $ kfacts k))
          return (k', mapping)
    | otherwise =
        do
          let mapping = strandids k
          let i = inst (strand n)
          (gen', i') <- bldInstance (role i) (take p (trace i)) (gen k)
          let k' = deleteNodeRest k gen' (s, p)
                   (replaceNth i' s (insts k))
                   (shortenOrderings (s, p) (tc k))
                   (prob k)
                   (deleteNodeFacts s p (kfacts k))
          return (k', mapping)
    where
      p = pos n
      s = sid (strand n)

{--
candWithNeededFacts :: Candidate -> [Candidate]
candWithNeededFacts (k,sids) =
    map (\k' -> (k',sids)) $ simplify k
--}

-- Update orderings when a strand is eliminated (p == 0)
deleteOrderings :: Sid -> [Pair] -> [Pair]
deleteOrderings s ps =
    do
      p <- ps
      deleteOrdering p
    where
      deleteOrdering (n0@(s0, _), n1@(s1, _))
          | s == s0 || s == s1 = []
          | otherwise = [(adjust n0, adjust n1)]
      adjust n@(s', i')
          | s' > s = (s' - 1, i')
          | otherwise = n

-- Update orderings when a strand is shortened (p > 0)
shortenOrderings :: Node -> [Pair] -> [Pair]
shortenOrderings (s, i) ps =
    do
      pair <- ps
      shortenOrdering pair
    where
      shortenOrdering p@((s0, i0), (s1, i1))
          | s == s0 && i <= i0 = []
          | s == s1 && i <= i1 = []
          | otherwise = [p]

deleteNodeRest :: Preskel -> Gen -> Node -> [Instance] -> [Pair] ->
                  [Sid] -> [Fact] -> Preskel
deleteNodeRest k gen n insts' orderings prob facts =
    newPreskel gen (shared k) insts' orderings non' pnon' unique'
    uniqgen' absent' precur' genSt' conf'
    auth' facts prio' (Generalized (Deleted n)) [] (pprob k) prob (pov k)
    where
      -- Drop nons that aren't mentioned anywhere
      non' = filter mentionedIn (knon k)
      pnon' = filter mentionedIn (kpnon k)
      mentionedIn t = varSubset [t] terms

      terms = iterms insts'
      vs = instVars insts'
      f False _ = False
      f True t = t `elem` vs

      lostgen (s,i) t = case generationPos t (trace ((insts k) !! s)) of
                          Nothing -> False
                          Just pos -> i <= pos

      -- Drop uniques that aren't carried anywhere
      unique' = filter carriedIn (kunique k)
      carriedIn t = any (carriedBy t) terms
      uniqgen' = filter (not . (lostgen n)) (kuniqgen k)
      absent' = filter (\(x, y) -> not (lostgen n x) && mentionedIn x && mentionedIn y) (kabsent k)
      precur' = map (updateNode (fst n) (fst n)) $ L.delete n (kprecur k)
      -- Drop channel assumptions for non-existent channels
      chans = ichans insts'
      conf' = filter (flip elem chans) (kconf k)
      auth' = filter (flip elem chans) (kauth k)
      genSt' = filter (\t -> foldVars f True t) (kgenSt k)
      -- Drop unused priorities
      prio' = filter within (kpriority k)
      within ((s, i), _) =
        s < fst n || s == fst n && i < snd n

deleteStrandFacts :: Sid -> [Fact] -> [Fact]
deleteStrandFacts s facts =
  filter f facts
  where
    f (Fact _ ft) =
      all g ft
    g (FSid s') = s /= s'
    g (FTerm _) = True

-- Correct this!  When we know how to filter based on strand and
-- index.  !!!!
deleteNodeFacts :: Sid -> Int -> [Fact] -> [Fact]
deleteNodeFacts s p facts =
  filter f facts
  where
    f (Fact _ fts) = checkRest fts
    checkRest [] = True
    checkRest ((FSid s') : (FTerm t) : rest)
        | s == s' =
            case intOfIndex t of
              Just q -> q<p && checkRest rest
              Nothing -> checkRest rest
        | otherwise = checkRest rest
    checkRest (_ : rest) = checkRest rest

permOfSidList :: [Sid] -> Sid -> Sid
permOfSidList = (!!)

withCoreFacts :: Preskel -> Preskel
withCoreFacts k =
    case pov k of
      Nothing -> k              -- Can't recover pov
      Just k0 ->
          case L.length (prob k) == L.length (insts k0) of
            False -> error ("Strands.withCoreFacts:  Mapping from POV to skeleton wrong length, "
                            ++ show (prob k) ++ " should map "
                                   ++ (show (L.length (insts k0))) ++ " strands into "
                                          ++ (show (L.length (insts k))))
            True ->
                case (homomorphism k0 k (prob k)) of
                  [] -> k
                  (env : _) ->  -- If there are multiple envs, this
                                -- could mean that some don't extend
                                -- under *simplify* to a result k1
                                -- such that k0 -> k1 -> k.  The
                                -- latter may have made a different
                                -- choice of env in its facts.
                                -- (Delete this if it turns out
                                -- wrong.)
                      k { kfacts =
                              map (instUpdateFact env (permOfSidList (prob k)))
                                      (kfacts k0) }

-- Node ordering weakening

-- To weaken, create a candidate for each element in the current
-- ordering, which is already the result of a transitive reduction.
-- Weaken by computing the transitive closure of the ordering, and
-- then remove the selected element from the current ordering.  After
-- computing the transitive closure, filter out the edges that are not
-- well ordered, i.e. originate at a reception node or terminate at a
-- transmission node.  Also, filter out edges that link nodes in the
-- same strand.  The preskeleton constructor function performs a
-- transitive reduction on the generated ordering.

weakenOrderings :: Preskel -> [Candidate]
weakenOrderings k =
    map (weakenOrdering k) (orderings k)

weakenOrdering :: Preskel -> Pair -> Candidate
weakenOrdering k p =
    weaken k p (L.delete p (tc k))

weaken :: Preskel -> Pair -> [Pair] -> Candidate
weaken k p orderings =
    addIdentity k'
    where
      k' = newPreskel (gen k) (shared k) (insts k) orderings (knon k)
           (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
           (kgenSt k) (kconf k) (kauth k) (kfacts k) (kpriority k)
           (Generalized (Weakened p)) [] (pprob k) (prob k) (pov k)

-- Origination assumption forgetting

-- Delete each non-originating term that is not specified by a
-- role.  Do the same for each uniquely-originating term.

forgetAssumption :: Preskel -> [Candidate]
forgetAssumption k =
    forgetUniqueTerm k ++ forgetNonTerm k ++ forgetPnonTerm k ++
    forgetUniqgenTerm k

-- Non-originating terms

forgetNonTerm :: Preskel -> [Candidate]
forgetNonTerm k =
    map (addIdentity . delNon) (skelNons k)
    where
      delNon t =
          renewPreskel
          $ k { knon = L.delete t (knon k),
                operation = Generalized (Forgot t), krules = [] }

skelNons :: Preskel -> [Term]
skelNons k =
    filter (flip notElem ru) (knon k)
    where
      ru = [u | i <- insts k, u <- inheritRnon i]

-- Penetrator non-originating terms

forgetPnonTerm :: Preskel -> [Candidate]
forgetPnonTerm k =
    map (addIdentity . delPnon) (skelPnons k)
    where
      delPnon t =
          renewPreskel
          $ k { kpnon = L.delete t (kpnon k),
                operation = Generalized (Forgot t), krules = [] }

skelPnons :: Preskel -> [Term]
skelPnons k =
    filter (flip notElem ru) (kpnon k)
    where
      ru = [u | i <- insts k, u <- inheritRpnon i]

-- Uniquely-originating terms

forgetUniqueTerm :: Preskel -> [Candidate]
forgetUniqueTerm k =
    map (addIdentity . delUniq) (skelUniques k)
    where
      delUniq t =
          renewPreskel
          $ k { kunique = L.delete t (kunique k),
                operation = Generalized (Forgot t),
                krules = [] }

skelUniques :: Preskel -> [Term]
skelUniques k =
    filter (flip notElem ru) (kunique k)
    where
      ru = [u | i <- insts k, u <- inheritRunique i]

-- Uniquely-generating terms

forgetUniqgenTerm :: Preskel -> [Candidate]
forgetUniqgenTerm k =
    map (addIdentity . delUgen) (skelUniqgens k)
    where
      delUgen t =
          k { kuniqgen = L.delete t (kuniqgen k),
              operation = Generalized (Forgot t), krules = [] }

skelUniqgens :: Preskel -> [Term]
skelUniqgens k =
    filter (flip notElem ru) (kuniqgen k)
    where
      ru = [u | i <- insts k, u <- inheritRuniqgen i]

-- Variable separation

-- A location is a strand, a role variable, and a position in the term
-- associated with the role variable.

-- step one: extract places
--
-- for each maplet in each environment in each strand
--   for each variable V in the range of the maplet
--     let P be the places at which V occurs
--     associate V with the location described by each element in P
--
-- step two: generate preskeletons
--
-- for each variable V in the skeleton K
--  let V' be a clone of V
--  let L be the set of locations associated with V from above
--  for each subset L' of L
--    for each instance I in K
--      update the environment of I by replacing V' at the locations
--      given by L' that refer to I, and use the modified environment
--      to update the instance
--    let K' be the result of updating instances in K as above
--    if V occurs in non, add terms with V replaced by V' to
--      the non's of K'
--    if V occurs in unique, add terms with V replaced by V'
--      to the unique's of K'
--    add K' to the list of generated preskeletons

separateVariables :: Preskel -> [Candidate]
separateVariables k =
    do
      v <- kvars k
      separateVariable k (extractPlaces k) v

-- A location is a strand, a role variable, and a position in the term
-- associated with the role variable.

type Location = (Sid, Term, Place)

-- Returns a list of pairs.  For each occurrence of a preskeleton
-- variable in every instance, there is a pair where the first element
-- is the variable, and the second as the location at which it occurs.
extractPlaces :: Preskel ->
                 [(Term, Location)]
extractPlaces k =
    [ (var, (sid s, v, p)) |
      s <- strands k,
      (v, t) <- instAssocs (inst s),
      var <- foldVars (flip adjoin) [] t,
      not (isExpr var), -- Filter out due to bugs in the algebra module
      p <- places var t ]

instAssocs :: Instance -> [(Term, Term)]
instAssocs i =
    reify (rvars (role i)) (env i)

-- For each variable, generate candidates by generating a fresh
-- variable for subsets of the locations associated with the variable.
separateVariable :: Preskel -> [(Term, Location)] -> Term -> [Candidate]
separateVariable _ _ t | isChan t = [] -- Ignore channels
separateVariable _ _ t | isLocn t = [] -- Ignore locations
-- Ignore group elements because of bugs in the algebra module
separateVariable _ _ t | isExpr t = []
separateVariable k ps t =
    sepVar (locsFor ps t)
    where
      sepVar [] = []
      sepVar [_] = []
      sepVar locs =
          do
            locs' <- parts locs
            changeLocations k env gen'' t' locs'
      (gen'', env) = matchAlways t t' (gen', emptyEnv)
      parts locs = map (map (locs !!)) (subsets (length locs))
      (gen', t') = clone (gen k) t

-- Extract the locations for a given variable
locsFor :: [(Term, Location)] -> Term -> [Location]
locsFor ps t =
    map snd (filter (\(t', _) -> t == t') (reverse ps)) -- Why reverse?

matchAlways :: Term -> Term -> (Gen, Env) -> (Gen, Env)
matchAlways t t' env =
    case match t t' env of
      e : _ -> e
      [] -> error "Strand.matchAlways: bad match"

-- Change the given locations and create the resulting preskeleton
changeLocations :: Preskel -> Env -> Gen -> Term -> [Location] -> [Candidate]
changeLocations k env gen t locs =
    [addIdentity k0, addIdentity k1]
    where
      k0 = newPreskel gen' (shared k) insts' (orderings k) non pnon
           unique0 uniqgen0 (kabsent k) (kprecur k)
           (kgenSt k) (kconf k) (kauth k) (kfacts k) (kpriority k)
           (Generalized (Separated t))
           [] (pprob k) (prob k) (pov k)
      k1 = newPreskel gen' (shared k) insts' (orderings k) non pnon
           unique1 uniqgen1 (kabsent k) (kprecur k) (kgenSt k)
           (kconf k) (kauth k) facts (kpriority k) (Generalized (Separated t))
           [] (pprob k) (prob k) (pov k)
      (gen', insts') = changeStrands locs t gen (strands k)
      non = knon k ++ map (instantiate env) (knon k)
      pnon = kpnon k ++ map (instantiate env) (kpnon k)
      unique0 = kunique k ++ unique'
      unique1 = map (instantiate env) (kunique k) ++ unique'
      -- Ensure all role unique assumptions are in.
      unique' = concatMap inheritRunique insts'
      uniqgen0 = kuniqgen k ++ uniqgen'
      uniqgen1 = map (instantiate env) (kuniqgen k) ++ uniqgen'
      -- Ensure all role uniq gen assumptions are in.
      uniqgen' = concatMap inheritRuniqgen insts'
      facts = map (instFact env) (kfacts k)

changeStrands :: [Location] -> Term -> Gen -> [Strand] -> (Gen, [Instance])
changeStrands locs copy gen strands =
    case foldMapM (changeStrand locs copy) gen strands of
      i : _ -> i
      [] -> error "Strand.changeStrands: bad strand build"

-- Create an new environment incorporating changes, and from that,
-- create the new strand.
changeStrand :: [Location] -> Term -> Gen -> Strand -> [(Gen, Instance)]
changeStrand locs copy gen s =
    bldInstance (role i) trace'  gen'
    where
      i = inst s
      (gen', env') = foldl f (gen, emptyEnv)
             (map (changeMaplet locs copy (sid s)) (instAssocs i))
      f env (v, t) = matchAlways v t env
      trace' = map (evtMap $ instantiate env') trace
      trace = take (height i) (rtrace (role i))

-- Change a maplet
changeMaplet :: [Location] -> Term -> Sid -> (Term, Term) -> (Term, Term)
changeMaplet [] _ _ maplet = maplet
changeMaplet ((s', v', p) : locs) copy s (v, t) =
    changeMaplet locs copy s (v, t')
    where
      t' = if s' == s && v' == v then replace copy p t else t

-- Return the set of subsets of natural numbers less than n
subsets :: Int -> [[Int]]
subsets n
    | n < 0 = error $ "Utilities.subsets: Bad argument " ++ show n
    | n == 0 = []
    | otherwise =
        [n - 1] : subset ++ map (n - 1 :) subset
        where
          subset = subsets (n - 1)

-- Collapse a shape by unifying strands.

collapse :: Preskel -> [Preskel]
collapse k =
    [k' | s <- strandids k, s' <- nats s,
          k' <- collapseStrands k s s']

collapseStrands :: Preskel -> Sid -> Sid -> [Preskel]
collapseStrands k s s' =
    do
      (s, s', subst) <- unifyStrands k s s'
      prs <- ksubst (k, k { operation = Collapsed s s', krules = [] },
                     (0, 0), strandids k, emptySubst) subst
      prs <- compress True prs s s'
      prs <- skeletonize useThinningDuringCollapsing prs
      return $ skel prs

-- Facts

data FTerm
  = FSid Sid
  | FTerm Term
  deriving (Eq, Show)

data Fact
  = Fact String [FTerm]
  deriving (Eq, Show)

substFTerm :: Subst -> FTerm -> FTerm
substFTerm s (FTerm t) = FTerm $ substitute s t
substFTerm _ t = t

substFact :: Subst -> Fact -> Fact
substFact s (Fact name fs) = Fact name $ map (substFTerm s) fs

instFTerm :: Env -> FTerm -> FTerm
instFTerm s (FTerm t) = FTerm $ instantiate s t
instFTerm _ t = t

instFact :: Env -> Fact -> Fact
instFact s (Fact name fs) = Fact name $ map (instFTerm s) fs

updateFTerm :: (Sid -> Sid) -> FTerm -> FTerm
updateFTerm f (FSid s) = FSid $ f s
updateFTerm _ t = t

updateFact :: (Sid -> Sid) -> Fact -> Fact
updateFact f (Fact name fs) = Fact name $ map (updateFTerm f) fs

instUpdateFTerm :: Env -> (Sid -> Sid) -> FTerm -> FTerm
instUpdateFTerm _ f (FSid s) = FSid $ f s
instUpdateFTerm e _ (FTerm t) = FTerm $ instantiate e t

instUpdateFact :: Env -> (Sid -> Sid) -> Fact -> Fact
instUpdateFact e f (Fact name fs) = Fact name $ map (instUpdateFTerm e f) fs

instVars :: [Instance] -> [Term]
instVars insts =
    S.elems $ foldl addIvars S.empty insts

factVars :: [Instance] -> [Fact] -> [Term]
factVars insts facts =
  S.elems $ S.difference fvars ivars
  where
    ivars = foldl addIvars S.empty insts
    fvars = foldl addFvars S.empty facts

addFvars :: Set Term -> Fact -> Set Term
addFvars vs (Fact _ ts) =
  foldl f vs ts
  where
    f vs (FSid _) = vs
    f vs (FTerm t) = foldVars (flip S.insert) vs t

{-- For debugging
factVars :: Fact -> [Term] -> [Term]
factVars (Fact _ ts) vs =
  foldr f vs ts
  where
    f (FSid _) vs = vs
    f (FTerm t) vs = addVars vs t

chkFVars :: Preskel -> Preskel
chkFVars k =
  foldl f k (foldr factVars [] (kfacts k))
  where
    f k v
      | elem v (kvars k) = k
      | otherwise = error ("Bad var in fact " ++ show v)
--}

{-
chkFacts :: Preskel -> Bool
chkFacts k =
  all checkFact (kfacts k)
  where
    checkFact (Fact _ ft) =
      all checkFTerm ft
    checkFTerm (FSid s) =
      s < nstrands k
    checkFTerm (FNode (s, _)) =
      s < nstrands k
    checkFTerm (FTerm _) = True

-- Use this to find bad fact updates.
chkFacts :: Preskel -> Bool
chkFacts k =
  all checkFact (kfacts k)
  where
    checkFact (Fact _ ft) =
      all checkFTerm ft
    checkFTerm (FSid s) | s >= nstrands k = error "Bad strand in fact"
    checkFTerm (FNode (s, _)) | s >= nstrands k = error "Bad node in fact"
    checkFTerm _ = True

-}

-- Security goals: satisfaction of atomic formulas

-- Returns the environments that satisfy the antecedent
-- but do not extend to satisfy any of the conclusions.
--
goalSat :: Preskel -> Goal -> (Goal, [(Gen, Env)])
goalSat k g =
  (g, [ (gen, e) |
        (gen, e) <- conjoin (antec g) k (gen k, emptyEnv),
        conclusion (gen, e) ])
  where
    conclusion ge = all (disjunct ge) $ consq g
    disjunct ge (ebvs,a) = null $ conjoinEbvs a ebvs k ge

sat :: Preskel -> [(Goal, [(Gen, Env)])]
sat k =
  map (goalSat k) (kgoals k)

-- Conjunction

type Sem = Preskel -> (Gen, Env) -> [(Gen, Env)]

conjoin :: [AForm] -> Sem
conjoin [] _ ge = [ge]
conjoin (a: as) k ge =
  do
    ge <- checkSem (satisfy a []) k ge
    conjoin as k ge

conjoinEbvs :: [AForm] -> [Term] -> Sem
conjoinEbvs [] _ _ ge = [ge]
conjoinEbvs (a: as) ebvs k ge =
    do
    ge <- checkSem (satisfy a ebvs) k ge
    conjoinEbvs as ebvs k ge

-- Suppose a gen-env pair ge that satisfies the antecedent of a goal,
-- but does not extend to satisfy any of the disjuncts on the
-- conclusion.  We would like to know, for at least one disjunct of
-- the conclusion, say the first, an atomic formula in that disjunct
-- that cannot be satisfied.  unSatReport reports that.

unSatReport :: Preskel -> Goal -> (Gen, Env) -> AForm
unSatReport k g ge =
    case varAtomLists of
      [] -> AFact "false" []
      (ebvs,as) : _ -> iter ebvs as ge

    where
      varAtomLists = consq g

      -- doesn't happen if e is a counterexample
      iter _ [] _ = AFact "true" []
      iter ebvs (a : as) ge =
          case satisfy a ebvs k ge of
            [] -> a
            ge' : _ -> iter ebvs as ge'

-- Extends an environment (a variable assignment) according to the
-- given atomic formula.  The second argument is the set of
-- existentially bound variables, which we will use only in geq to
-- handle adding identities involving the existentially bound
-- variables.
satisfy :: AForm -> [Term] -> Sem
satisfy (Length r z h) _ = glength r z h
satisfy (Param r v i z t) _ = gparam r v i z t
satisfy (Prec n n') _ = gprec n n'
satisfy (Non t) _ = ggnon t
satisfy (Pnon t) _ = ggpnon t
satisfy (Uniq t) _ = gguniq t
satisfy (UniqAt t n) _ = guniqAt t n
satisfy (Ugen t) _ = gggen t
satisfy (UgenAt t n) _ = gugenAt t n
satisfy (GenStV t) _ = ggenstv t
satisfy (Conf t) _ = ggconf t
satisfy (Auth t) _ = ggauth t
satisfy (AFact name fs) _ = gafact name fs
satisfy (Equals t t') ebvs = geq ebvs t t'
satisfy (Component t t') _ = gcomponent t t'
satisfy (Commpair n n') _ = gcommpair n n'
satisfy (SameLocn n n') _ = gsamelocn n n'
satisfy (StateNode n) _ = gstateNode n
satisfy (Trans (t, t')) _ = gafact "trans" [t, t']
satisfy (LeadsTo n n') _ =
    \k ge ->
        do
          ge <- satisfy (Commpair n n') [] k ge
          ge <- satisfy (Prec n n') [] k ge
          ge <- satisfy (StateNode n) [] k ge
          -- Commpair entails StateNode n' too
          return ge

nodePairsOfSkel :: Preskel -> [Pair] -- Maybe ((Sid,Int),(Sid,Int))
nodePairsOfSkel k =
    let (g1,z1) = newVarDefault (gen k) "z1" "strd" in
    let (g2,z2) = newVarDefault g1 "z2" "strd" in
    let (g3,i1) = newVarDefault g2 "i1" "indx" in
    let (g4,i2) = newVarDefault g3 "i2" "indx" in

    (case mapM
              (\(_,e) ->
               tupleOfMaybeList
               (maybeList
                [strdLookup e z1, indxLookup e i1,
                 strdLookup e z2, indxLookup e i2]))
              (satisfy (LeadsTo (z1,i1) (z2,i2)) [] k (g4,emptyEnv)) of
       Nothing -> []
       Just l -> l)

    where
      maybeList [] = Just []
      maybeList (Nothing : _) = Nothing
      maybeList ((Just v) : l) =
          case maybeList l of
            Nothing -> Nothing
            Just l' -> Just (v : l')

      tupleOfMaybeList (Just [v1, v2, v3, v4]) = Just ((v1, v2), (v3, v4))
      tupleOfMaybeList (Just _) = Nothing
      tupleOfMaybeList Nothing = Nothing

glengthExtendEnv :: Role -> Term -> Sid -> Int -> Instance -> (Gen,Env) -> [(Gen,Env)]
glengthExtendEnv r z s h inst (g, e)
    | h > height inst = []
    | rname (role inst) == rname r = strdMatch z s (g, e)
    | otherwise =
        case bldInstance r (take h $ trace inst) g of -- See if z could have been an instance of r
          [] -> []
          _ -> strdMatch z s (g, e)

checkEnv :: Preskel -> Env -> Bool
checkEnv k e = strandBoundEnv e <= nstrands k

checkKFacts :: Preskel -> Bool
checkKFacts k =
    let bnd = nstrands k in
    let fterms = concatMap (\(Fact _ fts) -> fts) (kfacts k) in
    let strInds = L.map isStr fterms in
    L.all (\i -> i < bnd) strInds
    where
      isStr (FSid i) = i
      isStr _ = 0

checkBoth :: Preskel -> (Gen, Env) -> Bool
checkBoth k (_, e) =
    checkEnv k e && checkKFacts k

checkQuietly :: Preskel -> (Gen, Env) -> (Gen, Env)
checkQuietly k (g, e)
    | checkBoth k (g, e) = (g, e)
    | otherwise = localSignal k (g, e)

checkSem :: Sem -> Sem
checkSem f k (g, e)
    | checkBoth k (g, e) =
        L.map (checkQuietly k) $ f k (g, e)
    | otherwise = [localSignal k (g, e)]

localSignal :: Preskel -> (Gen, Env) -> (Gen, Env)
localSignal _ (g, e) =
--    z "yiao " (error ("localSignal: Env "  ++ (show e)))
  (g, e)

-- Role length predicate
-- r and h determine the predicate, which has arity one.
glength :: Role -> Term -> Term -> Sem
glength r z ht k (g, e) =
  case indxLookup e ht of
    Nothing -> []
    Just h  ->
      case strdLookup e z of
        Nothing ->
          do
            (s, inst) <- zip [0..] $ insts k
            glengthExtendEnv r z s h inst (g, e)
        Just s | s < nstrands k ->
          let inst = insts k !! s in
          glengthExtendEnv r z s h inst (g, e)
        _ -> []

-- Parameter predicate

-- r and t determine the predicate, which has arity two.  t must be a
-- variable declared in role r. h is the length of the smallest prefix
-- of the role's trace that contains t.
gparam :: Role -> Term -> Int -> Term -> Term -> Sem
gparam r t h z t' k (g, e) =
    case strdLookup e z of
      Nothing ->
          do
            (s, inst) <- zip [0..] $ insts k
            paramMatch r t h z s t' inst (g, e)
      Just s | s < nstrands k  ->
                 let inst = insts k !! s in
                 paramMatch r t h z s t' inst (g, e)
      _ -> []

paramMatch :: Role -> Term -> Int -> Term -> Int -> Term -> Instance -> (Gen,Env) ->  [(Gen,Env)]
paramMatch r pname h z s t' inst (g, e)
    | h > height inst = []
    | rname (role inst) == rname r =
        do
          ge <- strdMatch z s (g, e)
          match t' (instantiate (env inst) pname) ge
    | otherwise =
        do
          (g, inst) <- bldInstance r (take h $ trace inst) g
          ge <- strdMatch z s (g, e)
          match t' (instantiate (env inst) pname) ge

-- Node precedes
-- This looks at the transitive closure of the ordering graph.
gprec :: NodeTerm -> NodeTerm -> Sem
gprec n n' k (g, e) =
  case (nodeLookup e n, nodeLookup e n') of
    (Just p, Just p')
      | inSkel k p && inSkel k p' &&
        (strandPrec p p' || elem (p, p') tc) -> [(g, e)]
    _ ->
      do
        (p, p') <- tc
        (g, e) <- nodeMatch n p (g, e)
        nodeMatch n' p' (g, e)
  where
    tc = kgpOrdsAll k
         -- map graphPair $ graphCloseAll $ graphEdges $ strands k

inSkel :: Preskel -> (Int, Int) -> Bool
inSkel k (s, i) =
  s >= 0 && s < nstrands k && i >= 0 && i < height (insts k !! s)

strandPrec :: Node -> Node -> Bool
strandPrec (s, i) (s', i')
  | s == s' && i < i' = True
  | otherwise = False

nodeLookup :: Env -> NodeTerm -> Maybe Node
nodeLookup e (z, t) =
  do
    s <- strdLookup e z
    i <- indxLookup e t
    return (s, i)

nodeMatch :: NodeTerm -> Node -> (Gen, Env) -> [(Gen, Env)]
nodeMatch (z, t) (s, j) (g, e) =
  do
    (g,e) <- match t (indxOfInt j) (g, e)
    case indxLookup e t of
        Just i -> (case i == j of
                     True -> strdMatch z s (g, e)
                     False -> [])
        Nothing -> []

-- Non-origination
ggnon :: Term -> Sem
ggnon t k e =
  do
    t' <- knon k
    match t t' e

-- Penetrator non-origination
ggpnon :: Term -> Sem
ggpnon t k e =
  do
    t' <- kpnon k
    match t t' e

-- Unique origination
gguniq :: Term -> Sem
gguniq t k e =
  do
    t' <- kunique k
    match t t' e

-- Unique origination at a node
guniqAt :: Term -> NodeTerm -> Sem
guniqAt t (z, ht) k (g,e) =
  do
    (t', ls) <- korig k
    (g,e) <- match t t' (g,e)
    (case ls of
       [(s, j)] ->
           do
             (g,e) <- strdMatch z s (g,e)
             indxMatch ht j (g,e)
       _ -> [])

-- Unique generation
gggen :: Term -> Sem
gggen t k e =
  do
    t' <- kuniqgen k
    match t t' e

-- Unique origination at a node
gugenAt :: Term -> NodeTerm -> Sem
gugenAt t (z, ht) k (g,e) =
  do
    (t', ls) <- kugen k
    (g,e) <- match t t' (g,e)
    (case ls of
       [(s, j)] ->
           do
             (g,e) <- strdMatch z s (g,e)
             indxMatch ht j (g,e)
       _ -> [])

ggenstv :: Term -> Sem
ggenstv t k e =
  do
    t' <- kgenSt k
    match t t' e

-- Confidential channel
ggconf :: Term -> Sem
ggconf t k e =
  do
    t' <- kconf k
    match t t' e

-- Autheticated channel
ggauth :: Term -> Sem
ggauth t k e =
  do
    t' <- kauth k
    match t t' e

-- Facts
gafact :: String -> [Term] -> Sem
gafact name fs k e =
  do
    Fact name' ts <- kfacts k
    case name == name' of
      True -> fmatchList fs ts e
      False -> []

fmatchList :: [Term] -> [FTerm] -> (Gen, Env) -> [(Gen, Env)]
fmatchList [] [] e = [e]
fmatchList (f : fs) (t : ts) e =
  do
    e <- fmatch f t e
    fmatchList fs ts e
fmatchList _ _ _ = []

fmatch :: Term -> FTerm -> (Gen, Env) -> [(Gen, Env)]
fmatch z (FSid s) e =
  strdMatch z s e
fmatch t (FTerm t') e =
  match t t' e

-- Equality
geq :: [Term] -> Term -> Term -> Sem
geq ebvs t t' _ (g, e)
  -- Ensure all variables in t and t' are either in the domain of e,
  -- or else are among the existentially bound variables ebvs.
  -- This always happens for goals because they must be role specific
  -- but it is not always true for rules.
  | not (unmatchedVarsWithin e t ebvs) =
      error ("In a rule equality check, " ++
             "cannot find a binding for some variable in " ++ (show t) ++
             " with ebvs " ++ (show ebvs))
  | not (unmatchedVarsWithin e t' ebvs) =
      error ("In a rule equality check, " ++
             "cannot find a binding for some variable in " ++ (show t') ++
             "with ebvs " ++ (show ebvs))

  | ti == ti' = [(g, e)]
  | not (null ebvs) =
      filter (\(_,e') ->      -- where all modified vars are ebvs
                  envsAgreeOutside e e' ebvs)
      (L.map (\(g,s) ->
                 (g, substUpdate e s)) -- update the env with the
                                       -- subst
      $ unify t t' (g, emptySubst))

  | otherwise = []
  where
    ti = instantiate e t
    ti' = instantiate e t'

{--
  do
    subst <- unify t t' (g, emptySubst)
    return (fst subst, substUpdate e (snd subst))
--}

gcomponent :: Term -> Term -> Sem
gcomponent t t' k (g, e) =
    let result = foldl (\ges cmpt -> (geq [] t cmpt k (g, e)) ++ ges)
                 []
                 (components t') in
    --    z ("> " ++ (show (length result))) result
    result

--   satisfy (StateNode n) [] = gstateNode n

isStateChMsg :: ChMsg -> Bool
isStateChMsg (Plain _) = False
isStateChMsg (ChMsg c _) = isLocn c

nodeIsStateNode :: Preskel -> Node -> Bool
nodeIsStateNode k p =
    case dirChMsgOfNode p k of
      Nothing -> False
      Just (_,chm) -> isStateChMsg chm

gstateNode :: NodeTerm -> Sem
gstateNode n k (g, e) =
    case nodeLookup e n of
      Just p ->
          case nodeIsStateNode k p of
            True -> [(g,e)]
            False -> []
      Nothing ->
          do
            p <- filter (nodeIsStateNode k) $ genNodes k
            (g,e) <- nodeMatch n p (g,e)
            return (g, e)

nullSem :: Sem
nullSem _ _ = []

chMsgMatch :: ChMsg -> ChMsg -> Sem
chMsgMatch chmsg chmsg' k e =
    case chmsg of
      Plain m ->
          (case chmsg' of
             Plain m' ->
                 case m == m' of
                   True -> [e]
                   False -> nullSem k e
             ChMsg _ _ -> nullSem k e)
      ChMsg c m ->
          (case chmsg' of
             Plain _ -> nullSem k e
             ChMsg c' m' ->
                 case c == c' && m == m' of
                   True -> [e]
                   False -> nullSem k e)

dirMsgMatch :: Node -> Node -> Sem
dirMsgMatch p p' k e =
    case dirChMsgOfNode p k of
      Nothing -> []
      Just (Recv, _) -> []
      Just (Send, chmsg) ->
          case dirChMsgOfNode p' k of
            Nothing -> []
            Just (Send, _) -> []
            Just (Recv, chmsg') ->
                chMsgMatch chmsg chmsg' k e

gcommpair :: NodeTerm -> NodeTerm -> Sem
gcommpair n n' k (g, e) =
    case (nodeLookup e n, nodeLookup e n') of
      (Just p, Just p') -> dirMsgMatch p p' k (g, e)
      (Just p, Nothing) ->
          do
            p' <- genNodes k
            (g, e) <- nodeMatch n' p' (g, e)
            dirMsgMatch p p' k (g, e)
      (Nothing, Just p') ->
          do
            p <- genNodes k
            (g, e) <- nodeMatch n p (g, e)
            dirMsgMatch p p' k (g, e)
      (Nothing, Nothing) ->
          do
            p <- genNodes k
            (g, e) <- nodeMatch n p (g, e)
            p' <- genNodes k
            (g, e) <- nodeMatch n' p' (g, e)
            dirMsgMatch p p' k (g, e)

--   nodeSameLocn :: Node -> Node -> Preskel -> Bool
--   nodeSameLocn p p' k =
--       case dirChMsgOfNode p k of
--         Nothing -> False
--         Just (_, chmsg) ->
--             case dirChMsgOfNode p' k of
--               Nothing -> False
--               Just(_, chmsg') ->
--                   case (chmsg,chmsg') of
--                     (Plain _,_) -> False
--                     (_,Plain _) -> False
--                     (ChMsg c _, ChMsg c' _)
--                         | c == c' && isLocn c -> True
--                         | otherwise -> False

nodeLocn :: Node -> Preskel -> [Term]
nodeLocn (s,i) k =
    case dirChMsgOfNode (s,i) k of
      Nothing -> []
      Just (_, Plain _) -> []
      Just (_, ChMsg c _)
        | isLocn c -> [c]
        | otherwise -> []

glocnSem :: NodeTerm -> Preskel -> (Gen,Env) -> [(Term,(Gen,Env))]
glocnSem n k (g, e) =
    case nodeLookup e n of
      Just p ->
          do
            loc <- nodeLocn p k
            return (loc, (g, e))
      Nothing ->
          do
            p <- genNodes k
            loc <- nodeLocn p k
            (g, e) <- nodeMatch n p (g, e)
            return (loc, (g,e))

gsamelocn :: NodeTerm -> NodeTerm -> Sem
gsamelocn n n' k (g, e) =
    foldl
    (\so_far (l, (g, e)) ->
         (foldl
          (\so_far' (l',(g',e')) ->
               case l' == l of
                 True -> (g',e') : so_far'
                 False -> so_far')
          []
          (glocnSem n' k (g, e)))
         ++ so_far)
    []
    (glocnSem n k (g, e))

-- Rules

--   skelsIsomorphic :: Preskel -> Preskel -> Bool
--   skelsIsomorphic k k' =
--       (isomorphic (gist k) (gist k'))   -- previously k == k' || (isomorphic (gist k) (gist k'))

--   gistKnown :: Gist -> [(Preskel,Gist)] -> Bool
--   gistKnown g  =
--       any (\(_,g') -> isomorphic g g')
--
--   setModuloIso :: [Preskel] -> [Preskel]
--   setModuloIso ks =
--       ks'
--       where
--         (ks',_) =
--             unzip (foldl
--                    (\soFar (k,g) ->
--                         case gistKnown g soFar of
--                           True -> soFar
--                           False -> (k,g) : soFar)
--                    []
--                    $ L.zip ks (map gist ks))

{--
parFoldr :: (a -> b -> b) -> b -> [a] -> b
parFoldr _ b [] = b
parFoldr f b (a : as) =
    par b' (f a b')
    where
      b' = parFoldr f b as
--}

-- Suppose that eqRel is an equivalence relation, and one would like
-- to obtain sets modulo eqRel.  I.e. given a list l, one would like a
-- list l' such that everything in l bears the relation eqRel to
-- something in l', and no two items in l' bear eqRel to each other.

-- This procedure achieves that by a factoring the list by eqRel in
-- parallel, ie reducing the left and right halves and then merging.

mergeEqRel :: (a -> a -> Bool) -> [a] -> [a] -> [a]
mergeEqRel eqRel as bs =
    loop as []
    where
      loop [] keep = keep ++ bs
      loop (a:rest) keep =
          case any (eqRel a) bs of
            True -> loop rest keep
            False -> loop rest (a:keep)

parFactor :: (a -> a -> Bool) -> [a] -> [a]
parFactor _ [] = []
parFactor _ [a] = [a]
parFactor eqRel [a,b] =
    case eqRel a b of
      True -> [b]
      False -> [a,b]

parFactor eqRel as =
    mergeEqRel eqRel leftM rightM
    where
      (left,right) = L.splitAt ((L.length as) `div` 2) as
      leftM = par rightM (parFactor eqRel left)
      rightM = (parFactor eqRel right)

-- Given a list of preskeletons, return a maximal sublist containing
-- no isomorphic members.

-- Computed in parallel via the pars in parFactor.

factorIsomorphic :: [Preskel] -> [Preskel]
factorIsomorphic =
    parFactor
    (\k1 k2 -> isomorphic (gist k1) (gist k2))

mergeIsomorphic :: [Preskel] -> [Preskel] -> [Preskel]
mergeIsomorphic =
    mergeEqRel
    (\k1 k2 -> isomorphic (gist k1) (gist k2))

factorIsomorphicPreskels :: [Preskel] -> [Preskel]
factorIsomorphicPreskels = factorIsomorphic

-- Try simplifying k if possible
simplify :: Preskel -> [Preskel]
simplify k =
    if checkNullary k
    then
        case rewrite $ withCoreFacts k of
          Nothing -> [k]
          Just ks -> ks
    else
        []

{--
  case rewriteNullary k of
    Nothing -> []               -- Big win:  false consequence
    Just k ->
        case rewrite $ withCoreFacts k of
          Nothing -> [k]
          Just ks -> ks
--}
checkNullary :: Preskel -> Bool
checkNullary k =
    L.and $ map inapplicable nrs
    where
      nrs = nullaryrules $ protocol k
      inapplicable nr = null $ conjoin (antec $ rlgoal nr) k (gen k, emptyEnv)

{--
rewriteNullary :: Preskel -> Maybe Preskel
rewriteNullary k =
    loop nrs
    where
      nrs = nullaryrules $ protocol k
      loop [] = Just k
      loop (nr : rest) =
          case conjoin (antec $ rlgoal nr) k (gen k, emptyEnv) of
            [] -> loop rest     -- antecedent: no satisfying instances
            _  -> Nothing       -- satisfying instances, hence false!
--}

data Ternary k = Unsat | Unch | Found k

rewriteUnary :: Preskel -> Ternary Preskel
rewriteUnary k =
    loop k urs False False
    where
      urs = unaryrules $ protocol k
      loop _ [] False False = Unch  -- (z "u" Unch)
      loop k [] False True =
          case preskelWellFormed k of
            True -> Found k     --  (z "_" )
            False -> Unsat
      loop k [] True b = loop k urs False b
      loop k (ur : rest) b b' =
          case tryRule k ur of
            [] -> loop k rest b b'
            vas -> -- z ("unary " ++ (rlname ur))
                   (case rewriteUnaryOne k ur vas of
                      Nothing -> Unsat -- (z "?" Unsat)
                      Just k' -> loop k' -- (z "/" k')
                                 rest True True)

-- only interested in case ur is unary:

rewriteUnaryOne :: Preskel -> Rule -> [(Gen, Env)] -> Maybe Preskel
rewriteUnaryOne k ur vas =
    case consq $ rlgoal ur of
      -- First the case where it's really unary
      [([],conjuncts)] ->
          foldM (rewriteUnaryOneOnce (rlname ur) conjuncts) k vas
      _ ->
          fail ("rewriteUnaryOne:  Hey, not really unary, rule " ++ (rlname ur))
    -- Screwed up set of unary rules in the last case.  Should never
    -- occur.

rewriteUnaryOneOnce :: String -> [AForm] -> Preskel -> (Gen, Env) -> Maybe Preskel
rewriteUnaryOneOnce _ [] k _ = Just k
rewriteUnaryOneOnce rn (a : as) k ge =
    case checkURewrite (urwt rn a) k ge of
      None -> Nothing
      Failing msg -> fail msg
      Some (k,ge) ->
          case preskelWellFormed k of
            False -> Nothing
            True ->
                case toSkeleton False (f k) of
                  []   -> Nothing
                  [k'] -> rewriteUnaryOneOnce rn as k' ge
                  l    -> fail ("rewriteUnaryOneOnce:  too many results from toSkeleton ("
                                ++ (show (L.length l)) ++ ")")
    where
      f k = k { krules = L.nub $ rn : krules k }

data URewriteVal = None | Some (Preskel, (Gen, Env)) | Failing String

type URewrite = Preskel -> (Gen, Env) -> URewriteVal

checkURewrite :: URewrite -> URewrite
checkURewrite f k (g, e)
    | checkBoth k (g, e) =
        case f k (g, e) of
          None -> None
          Failing st -> Failing st
          Some (k', (g', e'))
              | checkBoth k' (g', e') -> Some (k', (g', e'))
              | otherwise -> Some (k', (localSignal k' (g', e')))
    | otherwise = Some (k, (localSignal k (g, e)))

uconjoin :: String -> [AForm] -> URewrite
uconjoin _ [] k (g, e) = Some (k, (g, e))
uconjoin rule (af : rest) k (g, e) =
    case checkURewrite (urwt rule af) k (g, e) of
      Some (k', (g', e')) -> uconjoin rule rest k' (g', e')
      result -> result

urwt :: String -> AForm -> URewrite
urwt rule (Length r z ht) = urlength rule r z ht
urwt rule (Param r v i z t) = urparam rule r v i z t
urwt rule (Prec n n') = urprec rule n n'
urwt rule (Non t) = urnon rule t
urwt rule (Pnon t) = urpnon rule t
urwt rule (Uniq t) = uruniq rule t
urwt rule (UniqAt t n) = uruniqAt rule t n
urwt rule (Ugen t) = urugen rule t
urwt rule (UgenAt t n) = urugenAt rule t n
urwt rule (GenStV t) = urgenst rule t
urwt rule (Conf t) = urconf rule t
urwt rule (Auth t) = urauth rule t
urwt rule (AFact name fs) = urafact rule name fs
urwt rule (Equals t t') = ureq rule t t'
urwt rule (Component t t') =
    \_ _ -> error ("In rule " ++ rule ++ ", component in conclusion with" ++
                                  (show t) ++ ",  " ++ (show t'))
urwt rule (Commpair n n') = urcommpair rule n n'
urwt rule (SameLocn n n') = ursamelocn rule n n'
urwt rule (StateNode n) = urstateNode rule n
urwt rule (Trans (t,t')) = urafact rule "trans" [t, t']
urwt rule (LeadsTo n n') =
    uconjoin rule [(Commpair n n'), (Prec n n'), (StateNode n)]
    -- Commpair and StateNode n entails StateNode n' too

urlength :: String -> Role -> Term -> Term -> URewrite
urlength name r z ht k (g, e) =
  case indxLookup e ht of
    Nothing -> Failing ("In rule " ++ name ++ ", role length did not get a height")
    Just h ->
      case length (rtrace r) < h of
         True -> None
         False ->
           (case strdLookup e z of
            Just s ->                 -- Try to displace
              case rDisplace e k' ns s of
                []              -> None
                [kge] -> Some kge
                l     ->
                    error ("urlength:  Hey, rDisplace multiple results (" ++
                           (show (length l)) ++ ")")
              where
                k' = addStrand g k r h
                ns = nstrands k
            Nothing ->
                Failing ("urlength:  Hey, strand variable unbound " ++ (show z)))

urparam :: String -> Role -> Term -> Int -> Term -> Term -> URewrite
urparam rule r v h z t k (g, e) =
  case strdLookup e z of
    Just s ->
        do
          case rDisplace e k' ns s of
            []               -> None
            [(k, ge)]        ->
                (case rParam name k ge t t' of
                   []        -> None
                   [kge]  -> Some kge
                   l         -> error ("urparam:  Hey, rParam multiple results (" ++
                                       (show (length l)) ++ ")"))
            l                ->
                error ("urparam:  Hey, rDisplace multiple results (" ++
                       (show (length l)) ++ ")")
        where
          inst = strandInst k s
          t' = instantiate (env inst) v
          k' = addStrand g k r h
          ns = nstrands k
    Nothing ->
        Failing ("In rule " ++ rule ++
                 ", parameter predicate did not get a strand")

prevIn :: Instance -> Int -> Maybe Int
prevIn inst i =
    case inbnd ((trace inst) !! i) of
      Just _ -> Just i
      Nothing -> if 0 < i then prevIn inst (i-1)
                 else Nothing

succOut :: Instance -> Int -> Maybe Int
succOut inst i =
    case outbnd ((trace inst) !! i) of
      Just _ -> Just i
      Nothing -> if (i+1) < height inst then succOut inst (i+1)
                 else Nothing

urprec :: String -> NodeTerm -> NodeTerm -> URewrite
urprec rule (z, t) (z', t') k (g, e) =
    case (strdLookup e z, strdLookup e z', indxLookup e t, indxLookup e t') of
      (Just s, Just s', Just i, Just i')
        | badIndex k s i || badIndex k s' i' -> None
        | elem ((s, i), (s', i')) tc -> Some (k, (g, e))
        | otherwise ->
            case (succOut ((insts k) !! s) i,
                  prevIn ((insts k) !! s') i') of
              (Just i, Just i') ->
                  case normalizeOrderings True (((s, i), (s', i')) : orderings k) of
                    [] -> None
                    [orderings'] ->
                        let k' = newPreskel g (shared k) (insts k)
                                 orderings' (knon k) (kpnon k)
                                 (kunique k) (kuniqgen k) (kabsent k)
                                 (kprecur k) (kgenSt k) (kconf k) (kauth k)
                                 (kfacts k) (kpriority k) (operation k)
                                 (krules k) (pprob k) (prob k) (pov k) in
                        Some (k', (gen k, e))
                    l -> error ("urprec:  normalizeOrderings returned several orderings (" ++
                                (show (length l)) ++ ")")
              (_,_) -> None
      _ -> Failing ("In rule " ++ rule ++ ", precedence did not get a strand or a height")
    where
      tc = kgpOrds k
          -- map graphPair $ graphClose $ graphEdges $ strands k
    -- Observe here that we do not need graphCloseAll, since absent
    -- orderings that lie on the same strand are irreparable.

urnon :: String -> Term -> URewrite
urnon rule t k (g, e) =
    case matched e t of
      True
        | elem t' (knon k) -> Some (k, (g, e))
        | not $ isAtom t' -> None
        | otherwise ->
            Some (k', (g, e))
          where
            k' = newPreskel
                     g (shared k) (insts k) (orderings k) (t' : knon k)
                     (kpnon k) (kunique k) (kuniqgen k) (kabsent k)
                     (kprecur k) (kgenSt k) (kconf k) (kauth k) (kfacts k)
                     (kpriority k) (operation k) (krules k) (pprob k)
                     (prob k) (pov k)
      False ->
          Failing ("In rule " ++ rule ++ ", non did not get a term")
    where
      t' = instantiate e t

urpnon :: String -> Term -> URewrite
urpnon rule t k (g, e) =
    case matched e t of
      True
        | elem t' (kpnon k) -> Some (k, (g, e))
        | not $ isAtom t' -> None
        | otherwise ->
            Some (k', (g, e))
          where
            k' = newPreskel
                     g (shared k) (insts k) (orderings k) (knon k)
                     (t' : kpnon k) (kunique k) (kuniqgen k) (kabsent k)
                     (kprecur k) (kgenSt k) (kconf k) (kauth k) (kfacts k)
                     (kpriority k) (operation k) (krules k) (pprob k)
                     (prob k) (pov k)
      False ->
          Failing ("In rule " ++ rule ++ ", pnon did not get a term")
    where
      t' = instantiate e t

uruniq :: String -> Term -> URewrite
uruniq rule t k (g, e) =
    case matched e t of
      True
        | elem t' (kunique k) -> Some (k, (g, e))
        | not $ isAtom t' -> None
        | otherwise ->
            Some (k', (g, e))
          where
            k' = newPreskel
                     g (shared k) (insts k) (orderings k) (knon k)
                     (kpnon k) (t' : kunique k) (kuniqgen k) (kabsent k)
                     (kprecur k) (kgenSt k) (kconf k) (kauth k) (kfacts k)
                     (kpriority k) (operation k) (krules k) (pprob k)
                     (prob k) (pov k)
      False ->
          Failing ("In rule " ++ rule ++ ", uniq did not get a term")
    where
      t' = instantiate e t

uruniqAt :: String -> Term -> NodeTerm -> URewrite
uruniqAt rule t (z, ht) k (g, e) =
  case (matched e t, strdLookup e z, indxLookup e ht) of
    (False, _, _) ->
      Failing ("In rule " ++ rule ++ ", uniq-at did not get a term")
    (_, Nothing, _) ->
      Failing ("In rule " ++ rule ++ ", uniq-at did not get a strand")
    (_, _, Nothing) ->
        Failing ("In rule " ++ rule ++ ", uniq-at did not get an index")
    (True, Just s, Just i)
      | elem (t', [(s, i)]) (korig k) -> Some (k, (g, e))
      | not $ isAtom t'               -> None
      | i >= height (strandInst k s)  ->
          None                  -- Definitely None, since any
                                -- affirmative answer has to be
                                -- preserved by homomorphisms
      | checkOrigination t'
        (trace $ (insts k) !! s) i    ->
          let k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (t' : kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k) in
          Some (k', (g, e))
      | otherwise ->
          Failing ("In rule " ++ rule ++ ", uniq-at not at an origination")
      where
        t' = instantiate e t

urugen :: String -> Term -> URewrite
urugen rule t k (g, e) =
    case matched e t of
      True
        | elem t' (kuniqgen k) -> Some (k, (g, e))
        | not $ isAtom t' -> None
        | otherwise ->
            Some (k', (g, e))
          where
            k' = newPreskel
                     g (shared k) (insts k) (orderings k) (knon k)
                     (kpnon k) (kunique k) (t' : kuniqgen k) (kabsent k)
                     (kprecur k) (kgenSt k) (kconf k) (kauth k) (kfacts k)
                     (kpriority k) (operation k) (krules k) (pprob k)
                     (prob k) (pov k)
      False ->
          Failing ("In rule " ++ rule ++ ", ugen did not get a term")
    where
      t' = instantiate e t

urugenAt :: String -> Term -> NodeTerm -> URewrite
urugenAt rule t (z, ht) k (g, e) =
  case (matched e t, strdLookup e z, indxLookup e ht) of
    (False, _, _) ->
      Failing ("In rule " ++ rule ++ ", ugen-at did not get a term")
    (_, Nothing, _) ->
      Failing ("In rule " ++ rule ++ ", ugen-at did not get a strand")
    (_, _, Nothing) ->
        Failing ("In rule " ++ rule ++ ", ugen-at did not get an index")
    (True, Just s, Just i)
      | elem (t', [(s, i)]) (korig k) -> Some (k, (g, e))
      | not $ isAtom t'               -> None
      | i >= height (strandInst k s)  ->
          None                  -- Definitely None, since any
                                -- affirmative answer has to be
                                -- preserved by homomorphisms
      | checkGeneration t'
        (trace $ (insts k) !! s) i    ->
          let k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (kunique k) (t' : kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k) in
          Some (k', (g, e))
      | otherwise ->
          Failing ("In rule " ++ rule ++ ", ugen-at not at a generation")
      where
        t' = instantiate e t

urgenst :: String -> Term -> URewrite
urgenst rule t k (g, e) =
  case matched e t of
    True
      | elem t' (kgenSt k) -> Some (k, (g, e))
      | otherwise -> Some (k', (g, e))
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (adjoin t' $ kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      Failing ("In rule " ++ rule ++ ", genSt did not get a term")
  where
    t' = instantiate e t

urconf :: String -> Term -> URewrite
urconf rule t k (g, e) =
  case matched e t of
    True
      | elem t' (kconf k) -> Some (k, (g, e))
      | not $ isAtom t' -> None
      | otherwise -> Some (k', (g, e))
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k)
                  (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (t': kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      Failing ("In rule " ++ rule ++ ", conf did not get a term")
  where
    t' = instantiate e t

urauth :: String -> Term -> URewrite
urauth rule t k (g, e) =
  case matched e t of
    True
      | elem t' (kauth k) -> Some (k, (g, e))
      | not $ isAtom t' -> None
      | otherwise -> Some (k', (g, e))
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k)
                  (kpnon k) (kunique k) (kuniqgen k) (kabsent k)
                  (kprecur k)(kgenSt k) (kconf k) (t' : kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      Failing ("In rule " ++ rule ++ ", auth did not get a term")
  where
    t' = instantiate e t

urafact :: String -> String -> [Term] -> URewrite
urafact rule predname fts k (g, e)
  | elem fact (kfacts k) = Some (k, (g, e))
  | otherwise = Some (k', (gen k', e))
  where
    fts' = map (rFactLookup rule e) fts
    fact = Fact predname fts'
    k' = newPreskel
         g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
         (kunique k) (kuniqgen k) (kabsent k) (kprecur k) (kgenSt k)
         (kconf k) (kauth k) (L.nub $ fact : kfacts k)
         (kpriority k) (operation k) (krules k) (pprob k) (prob k) (pov k)

ureq :: String -> Term -> Term -> URewrite
ureq rule x y k (g, e)
    | isStrdVar x && isStrdVar y =
        case (strdLookup e x, strdLookup e y) of
          (Just s, Just t)
            | s == t -> Some (k, (g, e))
            | s < (L.length (insts k)) && t < (L.length (insts k))  ->
                (case rDisplace e (k {gen = g}) s t of
                  []              -> None
                  [(k', (g',e'))] -> Some (k', (g',e'))
                  l               ->
                      error ("ureq:  Hey, rDisplace multiple results (" ++
                             (show (length l)) ++ ")"))
            | not (checkKFacts k) -> error ("ureq:  Bad kfacts")
            | not (checkEnv k e) -> error ("ureq:  Bad env")
            | otherwise ->
                error ("ureq:  indices too large, (" ++ (show s) ++ ", " ++ (show t) ++
                       " in env " ++ (show (L.map (\i -> (rname (role i), env i))
                                                 (insts k))))
          _ -> Failing ("In rule " ++ rule ++ ", = did not get a strand")
    | isStrdVar x || isStrdVar y  = None
    | u == v = Some (k, (g, e))
    | otherwise =
        case rUnify k (g, e) u v of
          []          -> None
          [(k,(g,e))] -> Some (k,(g,e))
          l           -> error ("ureq:  Hey, rUnify multiple results (" ++
                                (show (length l)) ++ ")")
--             _ ->
--                 error ("In rule " ++ rule ++ ", = did not get a term, " ++
--                        (show x) ++ ", " ++ (show y) ++ ", " ++ (show e))
    where
      u = if matched e x
          then instantiate e x
          else x
      v = if matched e x
          then instantiate e y
          else y

urcommpair :: String -> NodeTerm -> NodeTerm -> URewrite
urcommpair rule n n' k (g, e) =
  case nodeLookup e n of
    Nothing -> Failing ("In rule " ++ rule ++ ", comm-pair did not get two node terms")
    (Just p) ->
        (case dirChMsgOfNode p k of
           Nothing -> None
           Just (Recv, _) -> None
           Just (Send, chmsg) ->
               (case nodeLookup e n' of
                  Nothing -> Failing ("In rule " ++ rule ++ ", comm-pair did not get two node terms")
                  Just p' ->
                      (case dirChMsgOfNode p' k of
                         Nothing -> None
                         Just (Send, _) -> None
                         Just (Recv, chmsg') ->
                             (case (chmsg, chmsg') of
                                (Plain _, ChMsg _ _) -> None
                                (ChMsg _ _, Plain _) -> None
                                (Plain m, Plain m')  -> ureq rule m m' k (g, e)
                                (ChMsg c m, ChMsg c' m') ->
                                    case ureq rule c c' k (g, e) of
                                      None -> None
                                      Failing st -> Failing st
                                      Some (k',(g',e')) ->
                                          ureq rule m m' k' (g',e')))))

ursamelocn :: String -> NodeTerm -> NodeTerm -> URewrite
ursamelocn rule n n' k (g, e) =
    case (nodeLookup e n, nodeLookup e n') of
      (Just (s,i), Just (s',i')) ->
          case (nodeLocn (s,i) k, nodeLocn (s',i') k) of
            ([c],[c']) -> ureq rule c c' k (g, e)
            (_,_) -> None
      (_,_) -> Failing ("In rule " ++ rule ++ ", same-locn did not get two node terms")

urstateNode :: String -> NodeTerm -> URewrite
urstateNode rule n k (g, e) =
    case nodeLookup e n of
      Just (s,i) ->
          (case nodeIsStateNode k (s,i) of
             True -> Some (k, (g, e))
             False -> None)
      _ -> Failing ("In rule " ++ rule ++ ", state-node did not get a node term")

rewriteDepthCount :: Int
rewriteDepthCount = 2000  -- was 14 and 24, 36

-- Try all rules associated with the protocol of k.

-- Return Nothing if no rule applies, otherwise return Just the list
-- of (zero or more) replacements.
rewrite :: Preskel -> Maybe [Preskel]
rewrite k =
    case nullUnary k of         --  (z "<" k)
      Just [] -> Just []        -- z ">>" (Just [])
      Just [k'] -> iterate rewriteDepthCount [k'] [] True
      Nothing -> iterate rewriteDepthCount [k] [] False
      Just ks -> error ("rewrite:  nullUnary returned too many results ("
                        ++ (show (L.length ks)) ++ ")")
    where
      grules = generalrules $ protocol k

      nullUnary k =
          if checkNullary k
          then
              case rewriteUnary k of
                  Unsat    -> Just []
                  Unch     -> Nothing
                  Found k' -> Just [k']
          else
              Just []

      nullUnaryThrough =
          concatMap (\k -> maybe [k] id (nullUnary k))

      -- iterate todos done action, which yields Maybe [Preskel]
      iterate _ [] [_] False = Nothing          -- z ">>" Nothing
      iterate _ [] done False = error ("rewrite: non-singleton results with no change???  (" ++
                                        (show (L.length done)) ++ ")")
      iterate _ [] done True = Just done        -- z ">" (Just done)
      iterate 0 todos done True = Just (todos ++ done)  -- z ">!" (Just (todos ++ done))
      iterate 0 _ done False = error ("rewrite: exhausted depth bound with no action???  (" ++
                                        (show (L.length done)) ++ ")")
      iterate dc (k : rest) done b =
          case subiter k grules of
            Nothing  -> iterate (dc-1) rest (k : done) b
            Just new ->
                let new' = factorIsomorphic (nullUnaryThrough new) in
                -- nullUnaryThrough new in
                -- Could alternatively factor the new ones for
                -- isomorphic copies, but that sounds anomalous
                -- *Don't* Skip it for now.

                iterate dc -- (dc-1)
                            (mergeIsomorphic new' rest) done True

      -- subiter
      subiter _ [] = Nothing     -- No action, no rules left

      subiter k (r : rs) =
          case tryRule k r of
            [] -> subiter k rs
            vas ->
                (Just (concatMap (\k' -> maybe [k'] id
                                        $ subiter k' rs)
                     $ nullUnaryThrough
                           $ doRewrite k r vas))

-- Returns all environments that satisfy the antecedent
-- but do not extend to satisfy any of the conclusions.
--

tryRule :: Preskel -> Rule -> [(Gen, Env)]
tryRule k r =
  [(g, e) | (g, e) <- conjoin (antec $ rlgoal r) k (gen k, emptyEnv),
            conclusion (g, e) ]
  where
    conclusion e = all (disjunct e) $ consq $ rlgoal r
    disjunct e (ebvs,a) = null $ conjoinEbvs a ebvs k e

{--

ruleLimit :: Int
ruleLimit = 500

-- Repeatedly applies rules until no rule applies.
doRewrites :: [Rule] -> Preskel -> Rule -> [(Gen, Env)] -> [Preskel]
doRewrites rules k r vas =
  doRewritesLoop rules k (length vas) (doRewrite k r vas) []

doRewritesLoop :: [Rule] -> Preskel -> Int ->
                  [Preskel] -> [Preskel] -> [Preskel]
doRewritesLoop _ _ lim [] _
  | lim >= ruleLimit =
    error ("Aborting after applying " ++ show ruleLimit ++
           " rules and more are applicable (1)" -- ++ (show ks)
          )
doRewritesLoop _ _ lim _ _  -- todos ks
  | lim >= ruleLimit =
    error ("Aborting after applying " ++ show ruleLimit ++
           " rules and more are applicable "
           -- ++ (concatMap (\k' -> show (kfacts k')) (todos ++ ks))
          )
doRewritesLoop _ _ _ [] ks = reverse ks
doRewritesLoop rules k lim (k' : todo) ks =
  loop rules
  where
    loop [] =                   -- No rules apply
      doRewritesLoop rules k lim todo (k' : ks)
    loop (r : rs) =
      let vas = tryRule k' r in
        if null vas then
          loop rs               -- Rule does not apply
        else
          let new = doRewrite k' r vas in
            doRewritesLoop rules k (lim + length vas) (setModuloIso $ todo ++ new) (setModuloIso ks)

--}

-- Apply rewrite rule at all assignments
doRewrite :: Preskel -> Rule -> [(Gen, Env)] -> [Preskel]
doRewrite k r vas =
   --   concatMap (toSkeleton False) $
    concatMap (doRewriteOne k r) vas

-- Apply rewrite rule at one assignment
doRewriteOne :: Preskel -> Rule -> (Gen, Env) -> [Preskel]
doRewriteOne k r e =
  do
    (evars, cl) <- consq $ rlgoal r
    let e' = foldl fresh e evars
    (k, _) <- doConj (rlname r) cl k e'
    k <- wellFormedPreskel k
    k <- toSkeleton True k
    return $ f k                -- Add rule name
  where f k = k { krules = L.nub $ rlname r : krules k }

fresh :: (Gen, Env) -> Term -> (Gen, Env)
fresh (g, e) t
  | isStrdVar t = (g, e)
  | otherwise =
      case match t t' (g', e) of
        e' : _ -> e'
        [] -> error "Strand.fresh: Cannot match logical variable to clone"
    where
      (g', t') = clone g t

type Rewrite = Preskel -> (Gen, Env) -> [(Preskel, (Gen, Env))]

checkRewrite :: Rewrite -> Rewrite
checkRewrite f k (g, e)
    | checkBoth k (g, e) =
        L.map (\(k',(g',e')) -> (k', checkQuietly k' (g',e'))) $ f k (g, e)
    | otherwise = [(k, localSignal k (g, e))]

doConj :: String -> [AForm] -> Rewrite
doConj _ [] k e = [(k, e)]
doConj rule (f : fs) k e =
  do
    (k, e) <- checkRewrite (rwt rule f) k e
    doConj rule fs k e

rwt :: String -> AForm -> Rewrite
rwt rule (Length r z ht) = rlength rule r z ht
rwt rule (Param r v i z t) = rparam rule r v i z t
rwt rule (Prec n n') = rprec rule n n'
rwt rule (Non t) = rlnon rule t
rwt rule (Pnon t) = rlpnon rule t
rwt rule (Uniq t) = rluniq rule t
rwt rule (UniqAt t n) = runiqAt rule t n
rwt rule (Ugen t) = rlugen rule t
rwt rule (UgenAt t n) = rugenAt rule t n
rwt rule (GenStV t) = rlgenst rule t
rwt rule (Conf t) = rlconf rule t
rwt rule (Auth t) = rlauth rule t
rwt rule (AFact name fs) = rafact rule name fs
rwt rule (Equals t t') = req rule t t'
rwt rule (Component t t') =
    \_ _ -> error ("In rule " ++ rule ++ ", component in conclusion with" ++
                                  (show t) ++ ",  " ++ (show t'))
rwt rule (Commpair n n') = rcommpair rule n n'
rwt rule (SameLocn n n') = rsamelocn rule n n'
rwt rule (StateNode n) = rstateNode rule n
rwt rule (Trans (t,t')) = rafact rule "trans" [t, t']
rwt rule (LeadsTo n n') =
    \k ge ->
        do
          (k,ge) <- rwt rule (Commpair n n') k ge
          (k,ge) <- rwt rule (Prec n n') k ge
          (k,ge) <- rwt rule (StateNode n) k ge
          -- Commpair entails StateNode n' too
          return (k,ge)

rlength :: String -> Role -> Term -> Term -> Rewrite
rlength name r z ht k (g, e) =
  case indxLookup e ht of
    Nothing ->
        error ("In rule " ++ name ++ ", role length did not get a height")
    Just h ->
      case length (rtrace r) < h of
         True -> []
         False ->
           (case strdLookup e z of
            Just s ->                 -- Try to displace
              rDisplace e k' ns s
              where
                k' = addStrand g k r h
                ns = nstrands k
            Nothing ->                -- Try to augment
              do                      -- and displace everywhere
                let ns = nstrands k
                (g, e) <- strdMatch z ns (g, e)
                let k' = addStrand g k r h
                let f s' = rDisplace e k' ns s'
                (k', (gen k', e)) : concatMap f (nats ns))

-- Just add a strand cloned from a role.
-- The length must be greater than one.
addStrand :: Gen -> Preskel -> Role -> Int -> Preskel
addStrand g k r h =
  newPreskel g' (shared k) insts'
  (orderings k) non' pnon' unique' uniqgen' absent' (kprecur k)
  (kgenSt k) conf' auth' (kfacts k)
  (kpriority k) (operation k) (krules k) (pprob k) (prob k) (pov k)
  where
    (g', inst) = mkInstance g r emptyEnv h -- Create instance
    insts' = (insts k) ++ [inst]
    non' = inheritRnon inst ++ knon k
    pnon' = inheritRpnon inst ++ kpnon k
    unique' = inheritRunique inst ++ kunique k
    uniqgen' = inheritRuniqgen inst ++ kuniqgen k
    absent' = inheritRabsent inst ++ kabsent k
    conf' = inheritRconf inst ++ kconf k
    auth' = inheritRauth inst ++ kauth k

rDisplace :: Env -> Preskel -> Sid -> Sid -> [(Preskel, (Gen, Env))]
rDisplace e k s s' | s == s' = [(k, (gen k, e))]
rDisplace e k s s' =
  do
    (s, s', subst) <- unifyStrands k s s'
    k <- rSubst k subst
    k <- rCompress k s s'
    let e' = strdUpdate (substUpdate e (snd subst)) (updateStrand s s')
    let _ = checkSem (\_ ge -> [ge]) k ((gen k), e')
    return (k, (gen k, e'))

rSubst :: Preskel -> (Gen, Subst) -> [Preskel]
rSubst k (gen, subst) =
    do
      (gen', insts') <- foldMapM (substInst subst) gen (insts k)
      let non' = map (substitute subst) (knon k)
      let pnon' = map (substitute subst) (kpnon k)
      let unique' = map (substitute subst) (kunique k)
      let uniqgen' = map (substitute subst) (kuniqgen k)
      let absent' = map (pairApp $ substitute subst) (kabsent k)
      let genStV' = map (substitute subst) (kgenSt k)
      let conf' = map (substitute subst) (kconf k)
      let auth' = map (substitute subst) (kauth k)
      let facts' = map (substFact subst) (kfacts k)
      let operation' = substOper subst (operation k)
      return $
        newPreskel gen' (shared k) insts' (orderings k)
        non' pnon' unique' uniqgen' absent' (kprecur k)
        genStV' conf' auth' facts' (kpriority k)
        operation' (krules k) (pprob k) (prob k) (pov k)

-- Does rCompress assume that s \not= s'?  s is old, s' is new
rCompress :: Preskel -> Sid -> Sid -> [Preskel]
rCompress k s s' =
    do
      let perm = updatePerm s s' (strandids k)
      orderings' <- normalizeOrderings True
                    (permuteOrderings perm (orderings k))
      return $
        newPreskel
        (gen k)
        (shared k)
        (deleteNth s (insts k))
        orderings'
        (knon k)
        (kpnon k)
        (kunique k)
        (kuniqgen k)
        (kabsent k)
        (map (permuteNode perm) (kprecur k))
        (kgenSt k)
        (kconf k)
        (kauth k)
        (map (updateFact $ updateStrand s s') (kfacts k))
        (updatePriority perm (kpriority k))
        (operation k)
        (krules k)
        (pprob k)
        (updateProb perm (prob k))
        (pov k)

rparam :: String -> Role -> Term -> Int -> Term -> Term -> Rewrite
rparam name r v h z t k (g, e) =
  case strdLookup e z of
    Just s
      | height inst < h -> []   -- JDG:  This looks suspicious.  Why
                                -- not extend the inst to a greater
                                -- height?
      | rname (role inst) == rname r ->
        rParam name k (g, e) t t'
      | otherwise ->
        do
          (k, (g, e)) <- rDisplace e k' ns s
          rParam name k (g, e) t t'
      where
        inst = strandInst k s
        t' = instantiate (env inst) v
        k' = addStrand g k r h
        ns = nstrands k
    Nothing ->
      error ("In rule " ++ name ++
             ", parameter predicate did not get a strand")

rParam :: String -> Preskel -> (Gen, Env) ->
          Term -> Term -> [(Preskel, (Gen, Env))]
rParam name k (g, e) t t' =
  case matched e t of
    True ->
      rUnify k (g, e) (instantiate e t) t'
    False ->
      error ("In rule " ++ name ++
             ", parameter predicate did not get a value")

rUnify :: Preskel -> (Gen, Env) -> Term -> Term -> [(Preskel, (Gen, Env))]
rUnify k (g, e) t t' =
  do
    subst <- unify t t' (g, emptySubst)
    k <- rSubst k subst
    return (k, (gen k, substUpdate e (snd subst)))

rprec :: String -> NodeTerm -> NodeTerm -> Rewrite
rprec name (z, t) (z', t') k (g, e) =
  case (strdLookup e z, strdLookup e z', indxLookup e t, indxLookup e t') of
    (Just s, Just s', Just i, Just i')
      | elem ((s, i), (s', i')) tc -> [(k, (g, e))]
      | badIndex k s i || badIndex k s' i' -> []
      | otherwise ->
          case (succOut ((insts k) !! s) i,
                prevIn ((insts k) !! s') i') of
            (Just i, Just i') ->
                do                      -- Add one ordering
                  orderings' <- normalizeOrderings True
                                (((s, i), (s', i')) : orderings k)
                  let k' = newPreskel g (shared k) (insts k) orderings'
                           (knon k) (kpnon k) (kunique k) (kuniqgen k)
                           (kabsent k) (kprecur k) (kgenSt k)
                           (kconf k) (kauth k) (kfacts k) (kpriority k)
                           (operation k) (krules k) (pprob k) (prob k) (pov k)
                  return (k', (gen k, e))
            (_,_) -> []
    _ ->
      error ("In rule " ++ name ++ ", precedence did not get a strand or a height")
  where
    tc = kgpOrds k
         -- map graphPair $ graphClose $ graphEdges $ strands k

         --   rprec :: String -> NodeTerm -> NodeTerm -> Rewrite
--   rprec name (z, i) (z', i') k (g, e) =
--     case (strdLookup e z, strdLookup e z') of
--       (Just s, Just s')
--         | elem ((s, i), (s', i')) tc -> [(k, (g, e))]
--         | badIndex k s i || badIndex k s' i' -> []
--         | otherwise ->
--           do                      -- Add one ordering
--             orderings' <- normalizeOrderings True
--                           (((s, i), (s', i')) : orderings k)
--             let k' = newPreskel
--                     g (shared k) (insts k) orderings' (knon k) (kpnon k)
--                     (kunique k) (kconf k) (kauth k) (kfacts k) (kpriority k)
--                     (operation k) (krules k) (pprob k) (prob k) (pov k)
--             return (k', (gen k, e))
--       _ ->
--         error ("In rule " ++ name ++ ", precedence did not get a strand")
--     where
--       tc = map graphPair $ graphClose $ graphEdges $ strands k

badIndex :: Preskel -> Sid -> Int -> Bool
badIndex k s i =
  i >= height (strandInst k s)

rlnon :: String -> Term -> Rewrite
rlnon name t k (g, e) =
  case matched e t of
    True
      | elem t' (knon k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (t' : knon k)
                  (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", non did not get a term")
  where
    t' = instantiate e t

rlpnon :: String -> Term -> Rewrite
rlpnon name t k (g, e) =
  case matched e t of
    True
      | elem t' (kpnon k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k)
                  (t' : kpnon k) (kunique k) (kuniqgen k) (kabsent k)
                  (kprecur k) (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", pnon did not get a term")
  where
    t' = instantiate e t

rluniq :: String -> Term -> Rewrite
rluniq name t k (g, e) =
  case matched e t of
    True
      | elem t' (kunique k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (t' : kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", uniq did not get a term")
  where
    t' = instantiate e t

checkOrigination :: Term -> Trace -> Int -> Bool
checkOrigination t c i =
    case originationPos t c of
      Nothing -> False
      Just j -> i == j

runiqAt :: String -> Term -> NodeTerm -> Rewrite
runiqAt name t (z, ht) k (g, e) =
  case (matched e t, strdLookup e z, indxLookup e ht) of
    (True, Just s, Just i)
      | elem (t', [(s, i)]) (korig k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | i >= height (strandInst k s) -> []
      | checkOrigination t' (trace (strandInst k s)) i ->
          let k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (t' : kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k) in
          [(k', (g, e))]
      | otherwise ->
          error ("In rule " ++ name ++ ", uniq-at not at an origination")
    (False, _, _) ->
      error ("In rule " ++ name ++ ", uniq-at did not get a term")
    (_, Nothing, _) ->
      error ("In rule " ++ name ++ ", uniq-at did not get a strand")
    (_, _, Nothing) ->
        error ("In rule " ++ name ++ ", uniq-at did not get an index")
  where
    t' = instantiate e t

rlugen :: String -> Term -> Rewrite
rlugen name t k (g, e) =
  case matched e t of
    True
      | elem t' (kuniqgen k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (kunique k) (t' : kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", ugen did not get a term")
  where
    t' = instantiate e t

checkGeneration :: Term -> Trace -> Int -> Bool
checkGeneration t c i =
    case generationPos t c of
      Nothing -> False
      Just j -> i == j

rugenAt :: String -> Term -> NodeTerm -> Rewrite
rugenAt name t (z, ht) k (g, e) =
  case (matched e t, strdLookup e z, indxLookup e ht) of
    (True, Just s, Just i)
      | elem (t', [(s, i)]) (kugen k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | i >= height (strandInst k s) -> []
      | checkGeneration t' (trace (strandInst k s)) i ->
          let k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (kunique k) (t' : kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k) in
          [(k', (g, e))]
      | otherwise ->
          error ("In rule " ++ name ++ ", ugen-at not at an origination")
    (False, _, _) ->
      error ("In rule " ++ name ++ ", ugen-at did not get a term")
    (_, Nothing, _) ->
      error ("In rule " ++ name ++ ", ugen-at did not get a strand")
    (_, _, Nothing) ->
        error ("In rule " ++ name ++ ", ugen-at did not get an index")
  where
    t' = instantiate e t

rlgenst :: String -> Term -> Rewrite
rlgenst name t k (g, e) =
  case matched e t of
    True
      | elem t' (kgenSt k) -> [(k, (g, e))]
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
                  (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (adjoin t' $ kgenSt k) (kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", genSt did not get a term")
  where
    t' = instantiate e t

rlconf :: String -> Term -> Rewrite
rlconf name t k (g, e) =
  case matched e t of
    True
      | elem t' (kconf k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k)
                  (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (t': kconf k) (kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", conf did not get a term")
  where
    t' = instantiate e t

rlauth :: String -> Term -> Rewrite
rlauth name t k (g, e) =
  case matched e t of
    True
      | elem t' (kauth k) -> [(k, (g, e))]
      | not $ isAtom t' -> []
      | otherwise ->
        [(k', (g, e))]
        where
          k' = newPreskel
                  g (shared k) (insts k) (orderings k) (knon k)
                  (kpnon k) (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
                  (kgenSt k) (kconf k) (t' : kauth k) (kfacts k)
                  (kpriority k) (operation k) (krules k) (pprob k)
                  (prob k) (pov k)
    False ->
      error ("In rule " ++ name ++ ", auth did not get a term")
  where
    t' = instantiate e t

rafact :: String -> String -> [Term] -> Rewrite
rafact rule name fts k (g, e)
  | elem fact (kfacts k) = [(k, (g, e))]
  | otherwise = [(k', (gen k', e))]
  where
    fts' = map (rFactLookup rule e) fts
    fact = Fact name fts'
    k' = newPreskel
         g (shared k) (insts k) (orderings k) (knon k) (kpnon k)
         (kunique k) (kuniqgen k) (kabsent k) (kprecur k)
         (kgenSt k) (kconf k) (kauth k) (L.nub $ fact : kfacts k)
         (kpriority k) (operation k) (krules k) (pprob k) (prob k) (pov k)

rFactLookup :: String -> Env -> Term -> FTerm
rFactLookup name e t
  | isStrdVar t =
    case strdLookup e t of
      Just s -> FSid s
      Nothing ->
        error ("In rule " ++ name ++ ": fact did not get a strand")
  | matched e t = FTerm $ instantiate e t
  | otherwise =
      error ("In rule " ++ name ++ ": fact did not get a term")

req :: String -> Term -> Term -> Rewrite
req name x y k (g, e)
  | isStrdVar x =
    case (strdLookup e x, strdLookup e y) of
      (Just s, Just t)
        | s == t -> [(k, (g, e))]
        | s < (L.length (insts k)) && t < (L.length (insts k)) ->
          rDisplace e (k {gen = g})  s t
        | otherwise ->
            error ("req:  indices too large, (" ++ (show s) ++ ", " ++ (show t) ++ " in env " ++ (show e))
      _ ->
        error ("In rule " ++ name ++ ", = did not get a strand")
  | otherwise =
    case (matched e x, matched e y) of
      (True, True)
        | u == v -> [(k, (g, e))]
        | otherwise ->
          rUnify k (g, e) u v
      _ ->
        error ("In rule " ++ name ++ ", = did not get a term")
    where
      u = instantiate e x
      v = instantiate e y

rcommpair :: String -> NodeTerm -> NodeTerm -> Rewrite
rcommpair name n n' k (g, e) =
  case nodeLookup e n of
    Nothing -> error ("In rule " ++ name ++ ", comm-pair did not get two node terms")
    (Just p) ->
        (case dirChMsgOfNode p k of
           Nothing -> []
           Just (Recv, _) -> []
           Just (Send, chmsg) ->
               (case nodeLookup e n' of
                  Nothing -> error ("In rule " ++ name ++ ", comm-pair did not get two node terms")
                  Just p' ->
                      (case dirChMsgOfNode p' k of
                         Nothing -> []
                         Just (Send, _) -> []
                         Just (Recv, chmsg') ->
                             (case (chmsg, chmsg') of
                                (Plain _, ChMsg _ _) -> []
                                (ChMsg _ _, Plain _) -> []
                                (Plain m, Plain m')  -> req name m m' k (g, e)
                                (ChMsg c m, ChMsg c' m') ->
                                    do
                                      (k, (g,e)) <- req name c c' k (g, e)
                                      (k, (g,e)) <- req name m m' k (g, e)
                                      return (k, (g,e))))))

rsamelocn :: String -> NodeTerm -> NodeTerm -> Rewrite
rsamelocn name n n' k (g, e) =
    case (nodeLookup e n, nodeLookup e n') of
      (Just p, Just p') ->
          case (nodeLocn p k, nodeLocn p' k) of
            ([c],[c']) -> req name c c' k (g, e)
            (_,_) -> []
      (_,_) -> error ("In rule " ++ name ++ ", same-locn did not get two node terms")

rstateNode :: String -> NodeTerm -> Rewrite
rstateNode name n k (g, e) =
    case nodeLookup e n of
      Just p ->
          (case nodeIsStateNode k p of
             True -> [(k, (g, e))]
             False -> [])
      _ -> error ("In rule " ++ name ++ ", state-node did not get a node term")

applyLeadsTo :: Preskel -> [Pair] -> Preskel
applyLeadsTo k pairs =
    case rewriteUnaryOneOnce rn atomicFormulae k ge of
      Nothing -> k
      Just k' -> k'
    where
      rn = "(reading leads-to field)"
      ge = (gen k, emptyEnv)
      atomicFormulae =
          map commpairOfPair pairs
      commpairOfPair ((s1,i1), (s2,i2)) =
          Commpair (strdOfInt s1, indxOfInt i1)
                   (strdOfInt s2, indxOfInt i2)
