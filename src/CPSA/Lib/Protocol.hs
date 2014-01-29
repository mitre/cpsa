-- Protocol data structures.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Protocol (Event (..), evtTerm, evtMap, Trace, evt,
    tterms, originates, originationPos, acquiredPos, usedPos, Role,
    rname, rvars, rtrace, rnon, rpnon, runique, rcomment,
    rsearch, rnorig, rpnorig, ruorig, rpriority, mkRole, varSubset,
    varsInTerms, addVars, Prot, mkProt, pname, alg, pgen, roles,
    varsAllAtoms, pcomment, flow) where

import qualified Data.List as L
import qualified Data.Set as S
import Data.Set (Set)
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra

-- Useful operations on variables

-- Are the vars in ts a subset of the ones in ts'?
varSubset :: Algebra t p g s e c => [t] -> [t] -> Bool
varSubset ts ts' =
    all (flip elem (varsInTerms ts')) (varsInTerms ts)

varsInTerms :: Algebra t p g s e c => [t] -> [t]
varsInTerms ts =
    foldl addVars [] ts

addVars :: Algebra t p g s e c => [t] -> t -> [t]
addVars ts t = foldVars (flip adjoin) ts t

-- Message events and traces

data Event t
    = In !t                      -- Inbound message
    | Out !t                     -- Outbound messasge
      deriving (Show, Eq, Ord)

-- Dispatch to function based on direction.
evt :: (t -> a) -> (t -> a) -> Event t -> a
evt inDir outDir evt =
    case evt of
      In t -> inDir t
      Out t -> outDir t

-- Extract the term in an event (evt id id).
evtTerm :: Event t -> t
evtTerm (In t) = t
evtTerm (Out t) = t

-- Map the term in an event.
evtMap :: (t -> t) -> Event t -> Event t
evtMap f (In t) = In (f t)
evtMap f (Out t) = Out (f t)

-- A trace is a list of events.  The terms in the trace are
-- stored in causal order.
type Trace t = [Event t]

-- The set of terms in a trace.
tterms :: Eq t => Trace t -> [t]
tterms c =
    foldl (\ts evt -> adjoin (evtTerm evt) ts) [] c

-- Is the term carried by an event, and is the first one outgoing?
originates :: Algebra t p g s e c => t -> Trace t -> Bool
originates _ [] = False         -- Term is not carried
originates t (Out t' : c) = t `carriedBy` t' || originates t c
originates t (In t' : c) = not (t `carriedBy` t') && originates t c

-- At what position does a term originate in a trace?
originationPos :: Algebra t p g s e c => t -> Trace t -> Maybe Int
originationPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term is not carried
      loop pos (Out t' : c)
          | t `carriedBy` t' = Just pos -- Found it
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | t `carriedBy` t' = Nothing -- Term does not originate
          | otherwise = loop (pos + 1) c

-- At what position is a term acquired in a trace?
acquiredPos :: Algebra t p g s e c => t -> Trace t -> Maybe Int
acquiredPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term does not occur
      loop pos (In t' : c)
          | t `carriedBy` t' = Just pos -- Found it
          | t `occursIn` t' = Nothing   -- Occurs but is not carried
          | otherwise = loop (pos + 1) c
      loop pos (Out t' : c)
          | t `occursIn` t' = Nothing   -- Term occurs in outbound term
          | otherwise = loop (pos + 1) c

-- At what position do all of the variables in a term occur in a trace?
usedPos :: Algebra t p g s e c => t -> Trace t -> Maybe Int
usedPos t c =
    loop 0 (varsInTerms [t]) c
    where
      loop _ _ [] = Nothing
      loop pos vars (e : c) =
          let vars' = [ x | x <- vars, notElem x (varsInTerms [evtTerm e]) ] in
          case vars' of
            [] -> Just pos
            _ -> loop (pos + 1) vars' c

-- Data flow analysis of a trace.

-- Return the minimal sets of parameters computed using traceFlow
flow :: Algebra t p g s e c => Trace t -> [[t]]
flow c =
    toList $ filter minimal inits
    where
      inits = S.toList $ S.map fst $ traceFlow c (S.empty, S.empty)
      -- Is init minimal among sets in inits?
      minimal init = all (not . flip S.isProperSubsetOf init) inits
      -- Convert sets to lists and sort everything
      toList s = L.sort $ map (L.sort . S.toList) $ s

-- A flow rule maps an initial set of atoms and a set of available
-- terms to sets of pairs of the same sets.
type FlowRule t = (Set t, Set t) -> Set (Set t, Set t)

-- Analyze events in a trace sequentially
traceFlow :: Algebra t p g s e c => Trace t -> FlowRule t
traceFlow [] a = S.singleton a
traceFlow (d : c) a = comb (traceFlow c) (evtFlow d) a

-- Dispatch to algebra specific data flow routines
evtFlow :: Algebra t p g s e c => Event t -> FlowRule t
evtFlow (In t) = inFlow t
evtFlow (Out t) = outFlow t

-- Combine flow rules sequentially
comb :: Algebra t p g s e c => FlowRule t -> FlowRule t -> FlowRule t
comb f g x =
    S.fold h S.empty (g x)
    where h a s = S.union (f a) s

data Role t = Role
    { rname :: !String,
      rvars :: ![t],            -- Set of role variables
                                -- Events in causal order
      rtrace :: ![Event t],
      -- Set of non-originating atoms, possibly with a trace length
      rnon :: ![(Maybe Int, t)], -- that says when to inherit the atom
      rpnon :: ![(Maybe Int, t)], -- that says when to inherit the atom
      runique :: ![t],          -- Set of uniquely originating atoms
      rcomment :: [SExpr ()],   -- Comments from the input
      rsearch :: Bool, -- True when suggesting reverse test node search
      rnorig :: [(t, Int)],     -- Nons plus origination position
      rpnorig :: [(t, Int)], -- Penetrator nons plus origination position
      ruorig :: [(t, Int)],     -- Uniques plus origination position
      rpriority :: [Int] }      -- List of all priorities
    deriving Show

defaultPriority :: Int
defaultPriority = 5

-- The empty role name is used with listener strands.  All roles in a
-- protocol must have a name with more than one character.

-- The lists vars, non, pnon, and unique are sets and should never
-- contain duplicate terms.

-- Create a role
mkRole :: Algebra t p g s e c => String -> [t] -> Trace t ->
          [(Maybe Int, t)] -> [(Maybe Int, t)] -> [t] ->
          [SExpr ()] -> [(Int, Int)] -> Bool -> Role t
mkRole name vars trace non pnon unique comment priority rev =
    Role { rname = name,
           rvars = L.nub vars,  -- Every variable here must
           rtrace = trace,      -- occur in the trace.
           rnon = non,
           rpnon = pnon,
           runique = L.nub unique,
           rcomment = comment,
           rnorig = map addNonOrig $ nonNub non,
           rpnorig = map addNonOrig $ nonNub pnon,
           ruorig = map addUniqueOrig $ L.nub unique,
           rpriority = addDefaultPrio priority,
           rsearch = rev
         }
    where
      addUniqueOrig t =
          case originationPos t trace of
            Just p -> (t, p)
            Nothing -> error "Protocol.mkRole: Atom does not uniquely originate"
      addNonOrig (len, t) =
          case usedPos t trace of
            Nothing -> error "Protocol.mkRole: Atom variables not in trace"
            Just p ->
                case len of
                  Nothing -> (t, p)
                  Just len | len >= p -> (t, len)
                           | otherwise -> error msg
          where
            msg = "Protocol.mkRole: Position for atom too early in trace"
      -- Drop non-origination assumptions for the same atom.
      nonNub nons =
          reverse $ foldl f [] nons
          where
            f acc non@(_, t)
                | any (\(_, t') -> t == t') acc = acc
                | otherwise = non : acc
      addDefaultPrio priority =
          map f (nats $ length trace)
          where
            f n =
              case lookup n priority of
                Nothing -> defaultPriority
                Just p -> p

-- Protocols

data Prot t g
    = Prot { pname :: !String,  -- Name of the protocol
             alg :: !String,    -- Name of the algebra
             pgen :: !g,        -- Initial variable generator
             roles :: ![Role t],
             varsAllAtoms :: !Bool,   -- Are all role variables atoms?
             pcomment :: [SExpr ()] }  -- Comments from the input
    deriving Show

-- Callers should ensure every role has a distinct name.
mkProt :: Algebra t p g s e c => String -> String ->
          g -> [Role t] -> [SExpr ()] -> Prot t g
mkProt name alg gen roles comment =
    Prot { pname = name, alg = alg, pgen = gen,
           roles = roles, pcomment = comment,
           varsAllAtoms = all roleVarsAllAtoms roles }
    where
      roleVarsAllAtoms role = all isAtom (rvars role)
