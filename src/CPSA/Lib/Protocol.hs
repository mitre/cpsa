-- Protocol data structures.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Protocol (Event (..), evtTerm, evtMap, evt, inbnd, outbnd,
    Trace, tterms, originates,
    originationPos, acquiredPos, gainedPos, usedPos,
    Role, rname, rvars, rtrace, rnon, rpnon, runique, rcomment,
    rsearch, rnorig, rpnorig, ruorig, rpriority, mkRole, varSubset,
    varsInTerms, addVars,
    Prot, mkProt, pname, alg, pgen, roles, listenerRole,
    varsAllAtoms, pcomment) where

import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra

-- Useful operations on variables

-- Are the vars in ts a subset of the ones in ts'?
varSubset :: [Term] -> [Term] -> Bool
varSubset ts ts' =
    all (flip elem (varsInTerms ts')) (varsInTerms ts)

varsInTerms :: [Term] -> [Term]
varsInTerms ts =
    foldl addVars [] ts

addVars :: [Term] -> Term -> [Term]
addVars ts t = foldVars (flip adjoin) ts t

-- Message events and traces

data Event
    = In !Term                  -- Inbound message
    | Out !Term                 -- Outbound message
      deriving (Show, Eq, Ord)

-- Dispatch to function based on direction.
evt :: (Term -> a) -> (Term -> a) -> Event -> a
evt inDir outDir evt =
    case evt of
      In t -> inDir t
      Out t -> outDir t

-- Extract the term in an event (evt id id).
evtTerm :: Event -> Term
evtTerm (In t) = t
evtTerm (Out t) = t

-- Map the term in an event.
evtMap :: (Term -> Term) -> Event -> Event
evtMap f (In t) = In (f t)
evtMap f (Out t) = Out (f t)

-- Extract the term in an inbound event.
inbnd :: Event -> Maybe Term
inbnd (In t) = Just t
inbnd _ = Nothing

-- Extract the term in an outbound event.
outbnd :: Event -> Maybe Term
outbnd (Out t) = Just t
outbnd _ = Nothing

-- A trace is a list of events.  The terms in the trace are
-- stored in causal order.
type Trace = [Event]

-- The set of terms in a trace.
tterms :: Trace -> [Term]
tterms c =
    foldl (\ts evt -> adjoin (evtTerm evt) ts) [] c

-- Is the term carried by an event, and is the first one outgoing?
originates :: Term -> Trace -> Bool
originates _ [] = False         -- Term is not carried
originates t (Out t' : c) = t `carriedBy` t' || originates t c
originates t (In t' : c) = not (t `carriedBy` t') && originates t c

-- At what position does a term originate in a trace?
originationPos :: Term -> Trace -> Maybe Int
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
acquiredPos :: Term -> Trace -> Maybe Int
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

-- At what position is a term gained in a trace?
gainedPos :: Term -> Trace -> Maybe Int
gainedPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term is not carried
      loop pos (Out t' : c)
          | t `carriedBy` t' = Nothing -- Term is not gained
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | t `carriedBy` t' = Just pos -- Found it
          | otherwise = loop (pos + 1) c

-- At what position do all of the variables in a term occur in a trace?
usedPos :: Term -> Trace -> Maybe Int
usedPos t c =
    loop 0 (varsInTerms [t]) c
    where
      loop _ _ [] = Nothing
      loop pos vars (e : c) =
          let vars' = [ x | x <- vars, notElem x (varsInTerms [evtTerm e]) ] in
          case vars' of
            [] -> Just pos
            _ -> loop (pos + 1) vars' c

data Role = Role
    { rname :: !String,
      rvars :: ![Term],         -- Set of role variables
                                -- Events in causal order
      rtrace :: ![Event],
      -- Set of non-originating atoms, possibly with a trace length
      rnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      rpnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      runique :: ![Term],       -- Set of uniquely originating atoms
      rcomment :: [SExpr ()],   -- Comments from the input
      rsearch :: Bool, -- True when suggesting reverse test node search
      rnorig :: [(Term, Int)],  -- Nons plus origination position
      rpnorig :: [(Term, Int)], -- Penetrator nons plus origination position
      ruorig :: [(Term, Int)],  -- Uniques plus origination position
      rpriority :: [Int] }      -- List of all priorities
    deriving Show

defaultPriority :: Int
defaultPriority = 5

-- The empty role name is used with listener strands.  All roles in a
-- protocol must have a name with more than one character.

-- The lists vars, non, pnon, and unique are sets and should never
-- contain duplicate terms.

-- Create a role
mkRole :: String -> [Term] -> Trace ->
          [(Maybe Int, Term)] -> [(Maybe Int, Term)] -> [Term] ->
          [SExpr ()] -> [(Int, Int)] -> Bool -> Role
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

data Prot
    = Prot { pname :: !String,  -- Name of the protocol
             alg :: !String,    -- Name of the algebra
             pgen :: !Gen,      -- Initial variable generator
             roles :: ![Role], -- Non-listener roles of a protocol
             listenerRole :: Role,
             varsAllAtoms :: !Bool,   -- Are all role variables atoms?
             pcomment :: [SExpr ()] }  -- Comments from the input
    deriving Show

-- Callers should ensure every role has a distinct name.
mkProt :: String -> String -> Gen ->
          [Role] -> Role -> [SExpr ()] -> Prot
mkProt name alg gen roles lrole comment =
    Prot { pname = name, alg = alg, pgen = gen, roles = roles,
           listenerRole = lrole, pcomment = comment,
           varsAllAtoms = all roleVarsAllAtoms roles }
    where
      roleVarsAllAtoms role = all isAtom (rvars role)
