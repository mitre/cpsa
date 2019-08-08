-- Protocol data structures.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Protocol (Event (..), evtCm, evtTerm, evtChan, evtMap, evt,
    inbnd, outbnd, Trace, tterms, originates,
    originationPos, acquiredPos, gainedPos, usedPos,
    Role, rname, rvars, rtrace, rnon, rpnon, runique, rconf, rauth, rcomment,
    rsearch, rnorig, rpnorig, ruorig, rpconf, rpauth, rpriority, mkRole,
    tchans, varSubset, varsInTerms, addVars, firstOccurs,
    AForm (..), NodeTerm, Goal (..),
    aFormOrder, aFreeVars, Rule (..),
    Prot, mkProt, pname, alg, pgen, roles, rules, listenerRole,
    varsAllAtoms, pcomment) where

import qualified Data.List as L
import qualified Data.Maybe as M
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Channel

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
    = In !ChMsg                 -- Inbound message
    | Out !ChMsg                -- Outbound message
      deriving (Show, Eq, Ord)

-- Extract the channel message
evtCm :: Event -> ChMsg
evtCm (In t) =  t
evtCm (Out t) = t

-- Dispatch to function based on direction.
evt :: (Term -> a) -> (Term -> a) -> Event -> a
evt inDir outDir evt =
    case evt of
      In t -> inDir $ cmTerm t
      Out t -> outDir $ cmTerm t

-- Extract the term in an event (evt id id).
evtTerm :: Event -> Term
evtTerm (In t) = cmTerm t
evtTerm (Out t) = cmTerm t

-- Extract the channel in an event.
evtChan :: Event -> Maybe Term
evtChan (In t) = cmChan t
evtChan (Out t) = cmChan t

-- Map the term in an event.
evtMap :: (Term -> Term) -> Event -> Event
evtMap f (In t) = In (cmMap f t)
evtMap f (Out t) = Out (cmMap f t)

-- Extract the channel message in an inbound event.
inbnd :: Event -> Maybe ChMsg
inbnd (In t) = Just t
inbnd _ = Nothing

-- Extract the channel message in an outbound event.
outbnd :: Event -> Maybe ChMsg
outbnd (Out t) = Just t
outbnd _ = Nothing

-- A trace is a list of events.  The terms in the trace are
-- stored in causal order.
type Trace = [Event]

-- The set of terms in a trace.
tterms :: Trace -> [Term]
tterms c =
    foldl (\ts evt -> adjoin (evtTerm evt) ts) [] c

-- The set of channels in a term
tchans :: Trace -> [Term]
tchans c =
  L.nub $ M.catMaybes (map evtChan c)

-- Is the term carried by an event, and is the first one outgoing?
originates :: Term -> Trace -> Bool
originates _ [] = False         -- Term is not carried
originates t (Out t' : c) = t `carriedBy` cmTerm t' || originates t c
originates t (In t' : c) = not (t `carriedBy` cmTerm t') && originates t c

-- At what position does a term originate in a trace?
originationPos :: Term -> Trace -> Maybe Int
originationPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term is not carried
      loop pos (Out t' : c)
          | t `carriedBy` cmTerm t' = Just pos -- Found it
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | t `carriedBy` cmTerm t' = Nothing -- Term does not originate
          | otherwise = loop (pos + 1) c

-- At what position is a term acquired in a trace?
acquiredPos :: Term -> Trace -> Maybe Int
acquiredPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term does not occur
      loop pos (In t' : c)
          | t `carriedBy` cmTerm t' = Just pos -- Found it
          | t `occursIn` cmTerm t' = Nothing   -- Occurs but is not carried
          | otherwise = loop (pos + 1) c
      loop pos (Out t' : c)
          | t `occursIn` cmTerm t' = Nothing   -- Term occurs in outbound term
          | otherwise = loop (pos + 1) c

-- At what position is a term gained in a trace?
gainedPos :: Term -> Trace -> Maybe Int
gainedPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term is not carried
      loop pos (Out t' : c)
          | t `carriedBy` cmTerm t' = Nothing -- Term is not gained
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | t `carriedBy` cmTerm t' = Just pos -- Found it
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

-- At what position is a channel in a trace?
chanPos :: Term -> Trace -> Maybe Int
chanPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Channel is not in trace
      loop pos (Out t' : c)
          | Just t == cmChan t' = Just pos
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | Just t == cmChan t' = Just pos
          | otherwise = loop (pos + 1) c

data Role = Role
    { rname :: !String,
      rvars :: ![Term],         -- Set of role variables
                                -- Events in causal order
      rtrace :: ![Event],
      -- Set of non-originating atoms, possibly with a trace length
      rnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      rpnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      runique :: ![Term],       -- Set of uniquely originating atoms
      rconf :: ![Term],         -- Confidential channels
      rauth :: ![Term],         -- Authenticated channels
      rcomment :: [SExpr ()],   -- Comments from the input
      rsearch :: Bool, -- True when suggesting reverse test node search
      rnorig :: [(Term, Int)],  -- Nons plus origination position
      rpnorig :: [(Term, Int)], -- Penetrator nons plus origination position
      ruorig :: [(Term, Int)],  -- Uniques plus origination position
      rpconf :: [(Term, Int)],  -- Confidentials plus origination position
      rpauth :: [(Term, Int)],  -- Authenticated plus origination position
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
          | any (occursIn t) (cmTerms $ evtCm e) = Just i
          | otherwise = loop (i + 1) c

-- The empty role name is used with listener strands.  All roles in a
-- protocol must have a name with more than one character.

-- The lists vars, non, pnon, and unique are sets and should never
-- contain duplicate terms.

-- Create a role
mkRole :: String -> [Term] -> Trace ->
          [(Maybe Int, Term)] -> [(Maybe Int, Term)] -> [Term] -> [Term] ->
          [Term] -> [SExpr ()] -> [(Int, Int)] -> Bool -> Role
mkRole name vars trace non pnon unique conf auth comment priority rev =
    Role { rname = name,
           rvars = L.nub vars,  -- Every variable here must
           rtrace = trace,      -- occur in the trace.
           rnon = non,
           rpnon = pnon,
           runique = L.nub unique,
           rconf = L.nub conf,
           rauth = L.nub auth,
           rcomment = comment,
           rnorig = map addNonOrig $ nonNub non,
           rpnorig = map addNonOrig $ nonNub pnon,
           ruorig = map addUniqueOrig $ L.nub unique,
           rpconf = map addChanPos $ L.nub conf,
           rpauth = map addChanPos $ L.nub auth,
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
      addChanPos t =
        case chanPos t trace of
          Just p -> (t, p)
          Nothing -> error "Protocol.mkRole: Channel not in trace"
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

-- Security Goals

-- Syntax for the atomic formulas
data AForm
  = Length Role Term Int
  | Param Role Term Int Term Term -- role param first-height strand value
  | Prec NodeTerm NodeTerm
  | Non Term
  | Pnon Term
  | Uniq Term
  | UniqAt Term NodeTerm
  | Conf Term
  | Auth Term
  | AFact String [Term]
  | Equals Term Term
  deriving Show

type NodeTerm = (Term, Int)

data Goal
  = Goal { uvars :: [Term],          -- Universally quantified variables
           antec :: [AForm],         -- Antecedent
           -- Consequent with existentially quantified variables
           consq :: [([Term], [AForm])],
           concl :: [[AForm]] }      -- Conclusion
    deriving Show

-- Ordering used to sort by constructor order.
aFormOrder :: AForm -> AForm -> Ordering
aFormOrder (Length _ _ _) (Length _ _ _) = EQ
aFormOrder (Length _ _ _) (Param _ _ _ _ _) = LT
aFormOrder (Length _ _ _) (Prec _ _) = LT
aFormOrder (Length _ _ _) (Non _) = LT
aFormOrder (Length _ _ _) (Pnon _) = LT
aFormOrder (Length _ _ _) (Uniq _) = LT
aFormOrder (Length _ _ _) (UniqAt _ _) = LT
aFormOrder (Length _ _ _) (Conf _ ) = LT
aFormOrder (Length _ _ _) (Auth _) = LT
aFormOrder (Length _ _ _) (AFact _ _) = LT
aFormOrder (Length _ _ _) (Equals _ _) = LT
aFormOrder (Param _ _ _ _ _) (Length _ _ _) = GT
aFormOrder (Param _ _ _ _ _) (Param _ _ _ _ _) = EQ
aFormOrder (Param _ _ _ _ _) (Prec _ _) = LT
aFormOrder (Param _ _ _ _ _) (Non _) = LT
aFormOrder (Param _ _ _ _ _) (Pnon _) = LT
aFormOrder (Param _ _ _ _ _) (Uniq _) = LT
aFormOrder (Param _ _ _ _ _) (UniqAt _ _) = LT
aFormOrder (Param _ _ _ _ _) (Conf _ ) = LT
aFormOrder (Param _ _ _ _ _) (Auth _) = LT
aFormOrder (Param _ _ _ _ _) (AFact _ _) = LT
aFormOrder (Param _ _ _ _ _) (Equals _ _) = LT
aFormOrder (Prec _ _) (Length _ _ _) = GT
aFormOrder (Prec _ _) (Param _ _ _ _ _) = GT
aFormOrder (Prec _ _) (Prec _ _) = EQ
aFormOrder (Prec _ _) (Non _) = LT
aFormOrder (Prec _ _) (Pnon _) = LT
aFormOrder (Prec _ _) (Uniq _) = LT
aFormOrder (Prec _ _) (UniqAt _ _) = LT
aFormOrder (Prec _ _) (Conf _ ) = LT
aFormOrder (Prec _ _) (Auth _) = LT
aFormOrder (Prec _ _) (AFact _ _) = LT
aFormOrder (Prec _ _) (Equals _ _) = LT
aFormOrder (Non _) (Length _ _ _) = GT
aFormOrder (Non _) (Param _ _ _ _ _) = GT
aFormOrder (Non _) (Prec _ _) = GT
aFormOrder (Non _) (Non _) = EQ
aFormOrder (Non _) (Pnon _) = LT
aFormOrder (Non _) (Uniq _) = LT
aFormOrder (Non _) (UniqAt _ _) = LT
aFormOrder (Non _) (Conf _ ) = LT
aFormOrder (Non _) (Auth _) = LT
aFormOrder (Non _) (AFact _ _) = LT
aFormOrder (Non _) (Equals _ _) = LT
aFormOrder (Pnon _) (Length _ _ _) = GT
aFormOrder (Pnon _) (Param _ _ _ _ _) = GT
aFormOrder (Pnon _) (Prec _ _) = GT
aFormOrder (Pnon _) (Non _) = GT
aFormOrder (Pnon _) (Pnon _) = EQ
aFormOrder (Pnon _) (Uniq _) = LT
aFormOrder (Pnon _) (UniqAt _ _) = LT
aFormOrder (Pnon _) (Conf _ ) = LT
aFormOrder (Pnon _) (Auth _) = LT
aFormOrder (Pnon _) (AFact _ _) = LT
aFormOrder (Pnon _) (Equals _ _) = LT
aFormOrder (Uniq _) (Length _ _ _) = GT
aFormOrder (Uniq _) (Param _ _ _ _ _) = GT
aFormOrder (Uniq _) (Prec _ _) = GT
aFormOrder (Uniq _) (Non _) = GT
aFormOrder (Uniq _) (Pnon _) = GT
aFormOrder (Uniq _) (Uniq _) = EQ
aFormOrder (Uniq _) (UniqAt _ _) = LT
aFormOrder (Uniq _) (Conf _ ) = LT
aFormOrder (Uniq _) (Auth _) = LT
aFormOrder (Uniq _) (AFact _ _) = LT
aFormOrder (Uniq _) (Equals _ _) = LT
aFormOrder (UniqAt _ _) (Length _ _ _) = GT
aFormOrder (UniqAt _ _) (Param _ _ _ _ _) = GT
aFormOrder (UniqAt _ _) (Prec _ _) = GT
aFormOrder (UniqAt _ _) (Non _) = GT
aFormOrder (UniqAt _ _) (Pnon _) = GT
aFormOrder (UniqAt _ _) (Uniq _) = GT
aFormOrder (UniqAt _ _) (UniqAt _ _) = EQ
aFormOrder (UniqAt _ _) (Conf _ ) = LT
aFormOrder (UniqAt _ _) (Auth _) = LT
aFormOrder (UniqAt _ _) (AFact _ _) = LT
aFormOrder (UniqAt _ _) (Equals _ _) = LT
aFormOrder (Conf _ ) (Length _ _ _) = GT
aFormOrder (Conf _ ) (Param _ _ _ _ _) = GT
aFormOrder (Conf _ ) (Prec _ _) = GT
aFormOrder (Conf _ ) (Non _) = GT
aFormOrder (Conf _ ) (Pnon _) = GT
aFormOrder (Conf _ ) (Uniq _) = GT
aFormOrder (Conf _ ) (UniqAt _ _) = GT
aFormOrder (Conf _ ) (Conf _ ) = EQ
aFormOrder (Conf _ ) (Auth _) = LT
aFormOrder (Conf _ ) (AFact _ _) = LT
aFormOrder (Conf _ ) (Equals _ _) = LT
aFormOrder (Auth _) (Length _ _ _) = GT
aFormOrder (Auth _) (Param _ _ _ _ _) = GT
aFormOrder (Auth _) (Prec _ _) = GT
aFormOrder (Auth _) (Non _) = GT
aFormOrder (Auth _) (Pnon _) = GT
aFormOrder (Auth _) (Uniq _) = GT
aFormOrder (Auth _) (UniqAt _ _) = GT
aFormOrder (Auth _) (Conf _ ) = GT
aFormOrder (Auth _) (Auth _) = EQ
aFormOrder (Auth _) (AFact _ _) = LT
aFormOrder (Auth _) (Equals _ _) = LT
aFormOrder (AFact _ _) (Length _ _ _) = GT
aFormOrder (AFact _ _) (Param _ _ _ _ _) = GT
aFormOrder (AFact _ _) (Prec _ _) = GT
aFormOrder (AFact _ _) (Non _) = GT
aFormOrder (AFact _ _) (Pnon _) = GT
aFormOrder (AFact _ _) (Uniq _) = GT
aFormOrder (AFact _ _) (UniqAt _ _) = GT
aFormOrder (AFact _ _) (Conf _ ) = GT
aFormOrder (AFact _ _) (Auth _) = GT
aFormOrder (AFact _ _) (AFact _ _) = EQ
aFormOrder (AFact _ _) (Equals _ _) = LT
aFormOrder (Equals _ _) (Length _ _ _) = GT
aFormOrder (Equals _ _) (Param _ _ _ _ _) = GT
aFormOrder (Equals _ _) (Prec _ _) = GT
aFormOrder (Equals _ _) (Non _) = GT
aFormOrder (Equals _ _) (Pnon _) = GT
aFormOrder (Equals _ _) (Uniq _) = GT
aFormOrder (Equals _ _) (UniqAt _ _) = GT
aFormOrder (Equals _ _) (Conf _ ) = GT
aFormOrder (Equals _ _) (Auth _) = GT
aFormOrder (Equals _ _) (AFact _ _) = GT
aFormOrder (Equals _ _) (Equals _ _) = EQ

aFreeVars :: [Term] -> AForm -> [Term]
aFreeVars vars (Length _ z _) = addVars vars z
aFreeVars vars (Param _ _ _ z t) = addVars (addVars vars z) t
aFreeVars vars (Prec (x, _) (y, _)) = addVars (addVars vars x) y
aFreeVars vars (Non t) = addVars vars t
aFreeVars vars (Pnon t) = addVars vars t
aFreeVars vars (Uniq t) = addVars vars t
aFreeVars vars (UniqAt t (z, _)) = addVars (addVars vars t) z
aFreeVars vars (Conf t) = addVars vars t
aFreeVars vars (Auth t) = addVars vars t
aFreeVars vars (AFact _ ft) = foldl addVars vars ft
aFreeVars vars (Equals x y) = addVars (addVars vars x) y

data Rule
  = Rule { rlname :: String,    -- Name of rule
           rlgoal :: Goal,      -- Sentence
           rlcomment :: [SExpr ()] }
    deriving Show

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

{- aFormOrder generator

-- Generate the aFormOrder relation from a list of constructors

module Main (main) where

main :: IO ()
main =
  mapM_ putStrLn $ map output comps

-- Format output
output :: (String, String, String) -> String
output (x, y, c) =
  "aFormOrder (" ++ x ++ ") (" ++ y ++ ") = " ++ c

-- Compute comparisons
comps :: [(String, String, String)]
comps = [ (x, y, show $ compare i j) |
          (x, i) <- pairs,
          (y, j) <- pairs ]

-- Add in list position
pairs :: [(String, Int)]
pairs = zip constrs [0..]

-- Constructors
constrs :: [String]
constrs = [
  "Length _ _ _",
  "Param _ _ _ _ _",
  "Prec _ _",
  "Non _",
  "Pnon _",
  "Uniq _",
  "UniqAt _ _",
  "Conf _ ",
  "Auth _",
  "AFact _ _",
  "Equals _ _" ]
-}
