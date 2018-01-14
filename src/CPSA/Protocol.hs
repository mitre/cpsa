-- Protocol data structures.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Protocol (Event (..), evtTerm, evtMap, evt, inbnd, outbnd,
    Trace, tterms, originates,
    originationPos, acquiredPos, gainedPos, usedPos,
    Role, rname, rvars, rtrace, rnon, rpnon, runique, rcomment,
    rsearch, rnorig, rpnorig, ruorig, rpriority, mkRole, varSubset,
    varsInTerms, addVars, firstOccurs,
    UVar, NodeUTerm, UTerm (..), UForm (..), Rule (..),
    Prot, mkProt, pname, alg, pgen, roles, rules, listenerRole,
    varsAllAtoms, pcomment) where

import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra

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

-- | Compute the index of the first event at which the given variable
-- occurs in a trace.
firstOccursAt :: Term -> Trace -> Maybe Int
firstOccursAt t c =
    loop 0 c
    where
      loop _ [] = Nothing
      loop i (e : c)
          | occursIn t (evtTerm e) = Just i
          | otherwise = loop (i + 1) c

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

firstOccurs :: Term -> Role -> Maybe Int
firstOccurs v r = firstOccursAt v (rtrace r)

-- Protocol Rules

-- This is an unsorted logic

type UVar = String

type NodeUTerm = (UVar, Int)

data UTerm
  = UVar UVar                   -- Strand and term variable
  | UInv UVar                   -- Inverse key term
  | UNode NodeUTerm             -- Nodes -- var must be strand var
  deriving Show

-- Syntax for the atomic unsorted formulas
data UForm
  = ULen Role UVar Int
    -- role param first-occurs-height strand value
  | UParam Role Term Int UVar UTerm
  | UPrec NodeUTerm NodeUTerm
  | UNon UTerm
  | UPnon UTerm
  | UUniq UTerm
  | UFact String [UTerm]
  | UEquals UTerm UTerm
  deriving Show

data Rule
  = Rule { uname :: String,      -- Rule name
           uantec :: [UForm],    -- Antecedent
           uconcl :: [[UForm]],  -- Conclusion (null is false)
           ucomment :: [SExpr ()] }
  deriving Show

{-
-- Ordering used to sort by constructor order.
uFormOrder :: UForm -> UForm -> Ordering
uFormOrder (ULen _ _ _) (ULen _ _ _) = EQ
uFormOrder (ULen _ _ _) (UParam _ _ _ _ _) = LT
uFormOrder (ULen _ _ _) (UPrec _ _) = LT
uFormOrder (ULen _ _ _) (UNon _) = LT
uFormOrder (ULen _ _ _) (UPnon _) = LT
uFormOrder (ULen _ _ _) (UUniq _) = LT
uFormOrder (ULen _ _ _) (UUniqAt _ _) = LT
uFormOrder (ULen _ _ _) (UFact _ _) = LT
uFormOrder (ULen _ _ _) (UEquals _ _) = LT
uFormOrder (UParam _ _ _ _ _) (ULen _ _ _) = GT
uFormOrder (UParam _ _ _ _ _) (UParam _ _ _ _ _) = EQ
uFormOrder (UParam _ _ _ _ _) (UPrec _ _) = LT
uFormOrder (UParam _ _ _ _ _) (UNon _) = LT
uFormOrder (UParam _ _ _ _ _) (UPnon _) = LT
uFormOrder (UParam _ _ _ _ _) (UUniq _) = LT
uFormOrder (UParam _ _ _ _ _) (UUniqAt _ _) = LT
uFormOrder (UParam _ _ _ _ _) (UFact _ _) = LT
uFormOrder (UParam _ _ _ _ _) (UEquals _ _) = LT
uFormOrder (UPrec _ _) (ULen _ _ _) = GT
uFormOrder (UPrec _ _) (UParam _ _ _ _ _) = GT
uFormOrder (UPrec _ _) (UPrec _ _) = EQ
uFormOrder (UPrec _ _) (UNon _) = LT
uFormOrder (UPrec _ _) (UPnon _) = LT
uFormOrder (UPrec _ _) (UUniq _) = LT
uFormOrder (UPrec _ _) (UUniqAt _ _) = LT
uFormOrder (UPrec _ _) (UFact _ _) = LT
uFormOrder (UPrec _ _) (UEquals _ _) = LT
uFormOrder (UNon _) (ULen _ _ _) = GT
uFormOrder (UNon _) (UParam _ _ _ _ _) = GT
uFormOrder (UNon _) (UPrec _ _) = GT
uFormOrder (UNon _) (UNon _) = EQ
uFormOrder (UNon _) (UPnon _) = LT
uFormOrder (UNon _) (UUniq _) = LT
uFormOrder (UNon _) (UUniqAt _ _) = LT
uFormOrder (UNon _) (UFact _ _) = LT
uFormOrder (UNon _) (UEquals _ _) = LT
uFormOrder (UPnon _) (ULen _ _ _) = GT
uFormOrder (UPnon _) (UParam _ _ _ _ _) = GT
uFormOrder (UPnon _) (UPrec _ _) = GT
uFormOrder (UPnon _) (UNon _) = GT
uFormOrder (UPnon _) (UPnon _) = EQ
uFormOrder (UPnon _) (UUniq _) = LT
uFormOrder (UPnon _) (UUniqAt _ _) = LT
uFormOrder (UPnon _) (UFact _ _) = LT
uFormOrder (UPnon _) (UEquals _ _) = LT
uFormOrder (UUniq _) (ULen _ _ _) = GT
uFormOrder (UUniq _) (UParam _ _ _ _ _) = GT
uFormOrder (UUniq _) (UPrec _ _) = GT
uFormOrder (UUniq _) (UNon _) = GT
uFormOrder (UUniq _) (UPnon _) = GT
uFormOrder (UUniq _) (UUniq _) = EQ
uFormOrder (UUniq _) (UUniqAt _ _) = LT
uFormOrder (UUniq _) (UFact _ _) = LT
uFormOrder (UUniq _) (UEquals _ _) = LT
uFormOrder (UUniqAt _ _) (ULen _ _ _) = GT
uFormOrder (UUniqAt _ _) (UParam _ _ _ _ _) = GT
uFormOrder (UUniqAt _ _) (UPrec _ _) = GT
uFormOrder (UUniqAt _ _) (UNon _) = GT
uFormOrder (UUniqAt _ _) (UPnon _) = GT
uFormOrder (UUniqAt _ _) (UUniq _) = GT
uFormOrder (UUniqAt _ _) (UUniqAt _ _) = EQ
uFormOrder (UUniqAt _ _) (UFact _ _) = LT
uFormOrder (UUniqAt _ _) (UEquals _ _) = LT
uFormOrder (UFact _ _) (ULen _ _ _) = GT
uFormOrder (UFact _ _) (UParam _ _ _ _ _) = GT
uFormOrder (UFact _ _) (UPrec _ _) = GT
uFormOrder (UFact _ _) (UNon _) = GT
uFormOrder (UFact _ _) (UPnon _) = GT
uFormOrder (UFact _ _) (UUniq _) = GT
uFormOrder (UFact _ _) (UUniqAt _ _) = GT
uFormOrder (UFact _ _) (UFact _ _) = EQ
uFormOrder (UFact _ _) (UEquals _ _) = LT
uFormOrder (UEquals _ _) (ULen _ _ _) = GT
uFormOrder (UEquals _ _) (UParam _ _ _ _ _) = GT
uFormOrder (UEquals _ _) (UPrec _ _) = GT
uFormOrder (UEquals _ _) (UNon _) = GT
uFormOrder (UEquals _ _) (UPnon _) = GT
uFormOrder (UEquals _ _) (UUniq _) = GT
uFormOrder (UEquals _ _) (UUniqAt _ _) = GT
uFormOrder (UEquals _ _) (UFact _ _) = GT
uFormOrder (UEquals _ _) (UEquals _ _) = EQ
-}

-- Protocols

data Prot
    = Prot { pname :: !String,  -- Name of the protocol
             alg :: !String,    -- Name of the algebra
             pgen :: !Gen,      -- Initial variable generator
             roles :: ![Role], -- Non-listener roles of a protocol
             listenerRole :: Role,
             rules :: ![Rule],  -- Protocol rules
             varsAllAtoms :: !Bool,   -- Are all role variables atoms?
             pcomment :: [SExpr ()] }  -- Comments from the input
    deriving Show

-- Callers should ensure every role has a distinct name.
mkProt :: String -> String -> Gen ->
          [Role] -> Role -> [Rule] -> [SExpr ()] -> Prot
mkProt name alg gen roles lrole rules comment =
    Prot { pname = name, alg = alg, pgen = gen, roles = roles,
           listenerRole = lrole, rules = rules, pcomment = comment,
           varsAllAtoms = all roleVarsAllAtoms roles }
    where
      roleVarsAllAtoms role = all isAtom (rvars role)
