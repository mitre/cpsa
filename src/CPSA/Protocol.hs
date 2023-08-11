-- Protocol data structures.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Protocol (Event (..), evtCm, evtTerm, evtChan, evtMap, evt,
    inbnd, outbnd, Trace, tterms, originates, originationPos,
    generates, generationPos, firstOccursPos,
    acquiredPos, gainedPos, genGainedPos, usedPos, insPrecedeOuts,
    Role, rname, rvars, rtrace, rnon, rpnon, runique, runiqgen, rabsent,
    rconf, rauth, rcomment, rsearch, rnorig, rpnorig, ruorig, rugen, rabs,
    rpconf, rpauth, rpriority, mkRole, tchans, varSubset, varsInTerms,
    addVars, firstOccurs, paramOfName, envsRoleParams,
    AForm (..), NodeTerm, Goal (..), Conj, fvsAForm, fvsConj, fvsAntec, fvsConsq,
    aFormOrder, aFreeVars, instantiateAForm, instantiateConj, Rule (..),
    Prot, mkProt, pname, alg, pgen, psig, roles,
    nullaryrules, unaryrules, generalrules, rules, userrules, generatedrules,
    listenerRole, varsAllAtoms, pcomment) where

import qualified Data.List as L
import qualified Data.Maybe as M
import qualified Data.Set as S
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Channel
import CPSA.Signature (Sig)

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

-- Also see showst
--}

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

-- Does the term occur in an event, and is the first one outgoing?
generates :: Term -> Trace -> Bool
generates _ [] = False         -- Term does not occur
generates t (Out t' : c) = t `constituent` cmTerm t' || generates t c
generates t (In t' : c) = not (t `constituent` cmTerm t') && generates t c

-- At what position does a term generate in a trace?
generationPos :: Term -> Trace -> Maybe Int
generationPos t c =
    loop 0 c
    where
      maybeInv = invertKey t

      testMaybe Nothing _ = False
      testMaybe (Just tInv) ct = tInv `constituent` ct
      test t ct = t `constituent` ct

      loop _ [] = Nothing       -- Term does not occur
      loop pos (Out t' : c)
          | test t (cmTerm t') ||
            testMaybe maybeInv (cmTerm t') = Just pos -- Found it
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | test t (cmTerm t') ||
            testMaybe maybeInv (cmTerm t') = Nothing -- Term does not generate
          | otherwise = loop (pos + 1) c

firstOccursPos :: Term -> Trace -> Maybe Int
firstOccursPos t c =
    loop 0 c
    where
      maybeInv = invertKey t

      testMaybe Nothing _ = False
      testMaybe (Just tInv) ct = tInv `occursIn` ct
      test t ct = t `occursIn` ct

      loop _ [] = Nothing       -- Term does not occur
      loop pos (Out t' : c)
          | test t (cmTerm t') ||
            testMaybe maybeInv (cmTerm t') = Just pos -- Found it
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | test t (cmTerm t') ||
            testMaybe maybeInv (cmTerm t') = Just pos -- Found it
                                                      -- incoming
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

-- At what position is a term gained in a trace?
genGainedPos :: Term -> Trace -> Maybe Int
genGainedPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term does not occur
      loop pos (Out t' : c)
          | t `constituent` cmTerm t' = Nothing -- Term is not gained
          | otherwise = loop (pos + 1) c
      loop pos (In t' : c)
          | t `constituent` cmTerm t' = Just pos -- Found it
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

insPrecedeOuts :: Int -> Int -> Trace -> Bool
insPrecedeOuts lower upper c =
    loopIns (upper-lower) (drop lower c)
    where
      loopIns _ [] = False    -- Ran out too soon
      loopIns u (In _ : c)
          | u==0 = True        -- Safely completed
          | otherwise =
              loopIns (u-1) c
      loopIns u (Out _ : c)
          | u==0 = True          -- Safely completed
          | otherwise =
              loopOuts (u-1) c

      loopOuts _ [] = False   -- Ran out too soon
      loopOuts _ (In _ : _) =
          False -- Whoa:  Went back to Ins
      loopOuts u (Out _ : c)
          | u==0 = True        -- Safely completed
          | otherwise =
              loopOuts (u-1) c

data Role = Role
    { rname :: !String,
      rvars :: ![Term],         -- Set of role variables
                                -- Events in causal order
      rtrace :: ![Event],
      -- Set of non-originating atoms, possibly with a trace length
      rnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      rpnon :: ![(Maybe Int, Term)], -- that says when to inherit the atom
      runique :: ![Term],       -- Set of uniquely originating atoms
      runiqgen :: ![Term],      -- Set of uniquely generated atoms
      rabsent :: ![(Term, Term)], -- Role absence
      rconf :: ![Term],         -- Confidential channels
      rauth :: ![Term],         -- Authenticated channels
      rcomment :: [SExpr ()],   -- Comments from the input
      rsearch :: Bool, -- True when suggesting reverse test node search
      rnorig :: [(Term, Int)],  -- Nons plus origination position
      rpnorig :: [(Term, Int)], -- Penetrator nons plus origination position
      ruorig :: [(Term, Int)],  -- Uniques plus origination position
      rugen :: [(Term, Int)],   -- Uniq gens plus generation position
      rabs :: [(Term, Term, Int)], -- Absent plus position
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
          [(Term, Term)] -> [Term] -> [Term] ->
          [SExpr ()] -> [(Int, Int)] -> Bool -> Role
mkRole name vars trace non pnon unique uniqgen absent
    conf auth comment priority rev =
    Role { rname = name,
           rvars = L.nub vars,  -- Every variable here must
           rtrace = trace,      -- occur in the trace.
           rnon = non,
           rpnon = pnon,
           runique = L.nub unique,
           runiqgen = uniqgen',
           rabsent = absent',
           rconf = L.nub conf,
           rauth = L.nub auth,
           rcomment = comment,
           rnorig = map addNonOrig $ nonNub non,
           rpnorig = map addNonOrig $ nonNub pnon,
           ruorig = map addUniqueOrig $ L.nub unique,
           rugen = map addUniqueGen uniqgen',
           rabs = map addAbsentPos absent',
           rpconf = map addChanPos $ L.nub conf,
           rpauth = map addChanPos $ L.nub auth,
           rpriority = addDefaultPrio priority,
           rsearch = rev
         }
    where
      uniqgen' = L.nub uniqgen
      absent' = L.nub (traceAbsent trace uniqgen' ++ absent)
      addUniqueOrig t =
          case originationPos t trace of
            Just p -> (t, p)
            Nothing -> error "Protocol.mkRole: Atom does not uniquely originate"
      addUniqueGen t =
          case generationPos t trace of
            Just p -> (t, p)
            Nothing -> error "Protocol.mkRole: Atom does not uniquely generate"
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
      addAbsentPos (x, y) =
          case (usedPos x trace, usedPos y trace) of
            (Just xp, Just yp) -> (x, y, max xp yp)
            _ -> error msg
          where
            msg = "Protocol.mkRole: Absence variable not in trace"
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

traceAbsent :: Trace -> [Term] -> [(Term, Term)]
traceAbsent trace ugens =
  concatMap indz_ininsts $ filter isNum ugens
  where
    indz_ininsts v =
      case generationPos v trace of
        Nothing -> error "Protocol.mkRole: Atom does not generate"
        Just p -> indz_ininsts_var v p
    -- ind-zero instances for a specific variable v that generates at height p
    indz_ininsts_var v p =
      map (\t -> (v, t)) (numsUpTo p)
    -- returns a list of numeric subterms of all messages prior to height p.
    numsUpTo p =
      S.toList $ foldl f S.empty $ take p trace
      where
        f ts evt = S.union ts $ subNums $ evtTerm evt

-- Return just the index of the first occurrence of v in the trace, or
-- nothing.
firstOccurs :: Term -> Role -> Maybe Int
firstOccurs v r = firstOccursAt v (rtrace r)

paramOfName :: String -> Role -> Maybe Term
paramOfName name rl =
    seek (rvars rl)
    where
      seek [] = Nothing
      seek (v : rest)
          | name == varName v = Just v -- $ z v v
          | otherwise = seek rest

paramVarPairs :: Role -> [Term] -> [(Term,Term)]
paramVarPairs rl =
    foldl
    (\soFar v ->
         case paramOfName (varName v) rl of
           Nothing -> soFar
           Just p -> (p,v) : soFar)
    []

envsRoleParams :: Role -> [Term] -> Env
envsRoleParams rl vars =
    envOfParamVarPairs $ paramVarPairs rl vars

{--
envsRoleParams rl g =
    foldl
    (\ges v -> concatMap
               (\ge -> case paramOfName (varName v) rl of
                         Just p ->
                             case match p v ge -- (z ("ingoing env: "
                                               -- ++ (show ge)) ge)
                             of
                               [] ->  -- debug with z ("?" ++ (varName v))
                                    [ge]
                               xs -> --  z ("! " ++ (show v) ++ " for " ++ (show p)
                                     -- ++ " in " ++ (show xs))
                                     xs
                         Nothing -> -- vars not locally bound may
                                    -- occur elsewhere in formula
                                   [ge])
               ges)
    [(g,emptyEnv)]
--}

-- Security Goals

-- Syntax for the atomic formulas
data AForm
  = Length Role Term Term
  | Param Role Term Int Term Term -- role param first-height strand value
  | Prec NodeTerm NodeTerm
  | Non Term
  | Pnon Term
  | Uniq Term
  | UniqAt Term NodeTerm
  | Ugen Term
  | UgenAt Term NodeTerm
  | GenStV Term
  | Conf Term
  | Auth Term
  | Commpair NodeTerm NodeTerm
  | SameLocn NodeTerm NodeTerm
  | StateNode NodeTerm
  | Trans NodeTerm
  | LeadsTo NodeTerm NodeTerm
  | AFact String [Term]
  | Equals Term Term
  | Component Term Term
  deriving Show

type NodeTerm = (Term, Term)

data Goal =
    Goal { uvars :: [Term],          -- Universally quantified variables
           antec :: [AForm],         -- Antecedent
           -- Consequent with existentially quantified variables
           consq :: [([Term], [AForm])],
           concl :: [[AForm]] }      -- Conclusion
    deriving Show

type Conj = [(Pos, AForm)]

--   -- A HornRule has at most one disjunct, no existential
--   data HornRule =
--       HornRule { hruvars :: [Term],          -- Universally quantified variables
--                  hrantec :: [AForm],         -- Antecedent
--                  -- Consequent has no existentially quantified variables
--                  hrconsq :: [AForm],         -- Conjunction of atomic
--                                              -- formulas
--                  hrname :: !String,
--                  hrcomment :: [SExpr ()] }
--       deriving Show
--
--   -- A general rule has more than one disjunct in conclusion,
--   -- or else existentially bound vars
--
--   data GenRule =
--       GenRule { gruvars :: [Term],          -- Universally quantified variables
--                 grantec :: [AForm],         -- Antecedent
--                 -- Consequent  with existentially quantified variables
--                 -- Outer list is disjuncts, each w existential bindings
--                 grconsq :: [([Term], [AForm])],
--                 grname :: !String,
--                 grcomment :: [SExpr ()] }
--       deriving Show
--
--
--   --   data Rule
--   --     = Rule { rlname :: String,    -- Name of rule
--   --              rlgoal :: Goal,      -- Sentence
--   --              rlcomment :: [SExpr ()] }
--   --       deriving Show

indexOfAForm :: AForm -> Int
indexOfAForm (Length _ _ _) = 0
indexOfAForm (Param _ _ _ _ _) = 1
indexOfAForm (Prec _ _) = 2
indexOfAForm (Non _) = 3
indexOfAForm (Pnon _) = 4
indexOfAForm (Uniq _) = 5
indexOfAForm (UniqAt _ _) = 6
indexOfAForm (GenStV _) = 7
indexOfAForm (Conf _) = 8
indexOfAForm (Auth _) = 9
indexOfAForm (Commpair _ _) = 10
indexOfAForm (SameLocn _ _) = 11
indexOfAForm (StateNode _) = 12
indexOfAForm (Trans _) = 13
indexOfAForm (LeadsTo _ _) = 14
indexOfAForm (AFact _ _) = 15
indexOfAForm (Equals _ _) = 16
indexOfAForm (Component _ _) = 17
indexOfAForm (Ugen _) = 18
indexOfAForm (UgenAt _ _) = 19

aFormOrder :: AForm -> AForm -> Ordering
aFormOrder f f' = compare (indexOfAForm f) (indexOfAForm f')
--
--       let i' =   in
--       case i == i' of
--         True -> EQ
--         False ->
--             (case i < i' of
--                True -> LT
--                False -> GT)

{--  -- Unmaintainable version that we had before!

-- Ordering used to sort by constructor order.
aFormOrder :: AForm -> AForm -> Ordering
aFormOrder (Length _ _ _) (Length _ _ _) = EQ
aFormOrder (Length _ _ _) (Param _ _ _ _ _) = LT
aFormOrder (Length _ _ _) (Prec _ _) = LT
aFormOrder (Length _ _ _) (Non _) = LT
aFormOrder (Length _ _ _) (Pnon _) = LT
aFormOrder (Length _ _ _) (Uniq _) = LT
aFormOrder (Length _ _ _) (UniqAt _ _) = LT
aFormOrder (Length _ _ _) (GenStV _) = LT
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
aFormOrder (Param _ _ _ _ _) (GenStV _) = LT
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
aFormOrder (Prec _ _) (GenStV _) = LT
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
aFormOrder (Non _) (GenStV _) = LT
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
aFormOrder (Pnon _) (GenStV _) = LT
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
aFormOrder (Uniq _) (GenStV _) = LT
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
aFormOrder (UniqAt _ _) (GenStV _ ) = LT
aFormOrder (UniqAt _ _) (Conf _ ) = LT
aFormOrder (UniqAt _ _) (Auth _) = LT
aFormOrder (UniqAt _ _) (AFact _ _) = LT
aFormOrder (UniqAt _ _) (Equals _ _) = LT
aFormOrder (GenStV _) (Length _ _ _) = GT
aFormOrder (GenStV _) (Param _ _ _ _ _) = GT
aFormOrder (GenStV _) (Prec _ _) = GT
aFormOrder (GenStV _) (Non _) = GT
aFormOrder (GenStV _) (Pnon _) = GT
aFormOrder (GenStV _) (Uniq _) = GT
aFormOrder (GenStV _) (UniqAt _ _) = GT
aFormOrder (GenStV _) (GenStV _ ) = EQ
aFormOrder (GenStV _) (Conf _ ) = LT
aFormOrder (GenStV _) (Auth _) = LT
aFormOrder (GenStV _) (AFact _ _) = LT
aFormOrder (GenStV _) (Equals _ _) = LT
aFormOrder (Conf _ ) (Length _ _ _) = GT
aFormOrder (Conf _ ) (Param _ _ _ _ _) = GT
aFormOrder (Conf _ ) (Prec _ _) = GT
aFormOrder (Conf _ ) (Non _) = GT
aFormOrder (Conf _ ) (Pnon _) = GT
aFormOrder (Conf _ ) (Uniq _) = GT
aFormOrder (Conf _ ) (UniqAt _ _) = GT
aFormOrder (Conf _ ) (GenStV _) = GT
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
aFormOrder (Auth _) (GenStV _) = GT
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
aFormOrder (AFact _ _) (GenStV _) = GT
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
aFormOrder (Equals _ _) (GenStV _) = GT
aFormOrder (Equals _ _) (Conf _ ) = GT
aFormOrder (Equals _ _) (Auth _) = GT
aFormOrder (Equals _ _) (AFact _ _) = GT
aFormOrder (Equals _ _) (Equals _ _) = EQ
--}

aFreeVars :: [Term] -> AForm -> [Term]
aFreeVars vars (Length _ z _) = addVars vars z
aFreeVars vars (Param _ _ _ z t) = addVars (addVars vars z) t
aFreeVars vars (Prec (x, i) (y, j)) = addVars (addVars (addVars (addVars vars x) y) i) j
aFreeVars vars (Non t) = addVars vars t
aFreeVars vars (Pnon t) = addVars vars t
aFreeVars vars (Uniq t) = addVars vars t
aFreeVars vars (UniqAt t (z, i)) = addVars (addVars (addVars vars t) z) i
aFreeVars vars (Ugen t) = addVars vars t
aFreeVars vars (UgenAt t (z, i)) = addVars (addVars (addVars vars t) z) i
aFreeVars vars (GenStV t) = addVars vars t
aFreeVars vars (Conf t) = addVars vars t
aFreeVars vars (Auth t) = addVars vars t
aFreeVars vars (AFact _ ft) = foldl addVars vars ft
aFreeVars vars (Equals x y) = addVars (addVars vars x) y
aFreeVars vars (Component x y) = addVars (addVars vars x) y
aFreeVars vars (Commpair (s,t) (s',t')) = addVars (addVars (addVars (addVars vars s) t) s') t'
aFreeVars vars (SameLocn (s,t) (s',t')) = addVars (addVars (addVars (addVars vars s) t) s') t'
aFreeVars vars (StateNode (s,t)) = addVars (addVars vars s) t
aFreeVars vars (Trans (s,t)) = addVars (addVars vars s) t
aFreeVars vars (LeadsTo (s,t) (s',t')) = addVars (addVars (addVars (addVars vars s) t) s') t'

instantiateAForm :: Env -> AForm -> AForm
instantiateAForm e (Length rl z v) =
    (Length rl (instantiate e z) (instantiate e v))
instantiateAForm e (Param rl p i z t) =
    (Param rl p i (instantiate e z) (instantiate e t))
instantiateAForm e (Prec (x, i) (y, j)) =
    (Prec
     ((instantiate e x), (instantiate e i))
     ((instantiate e y), (instantiate e j)))
instantiateAForm e (Non t) =
    (Non (instantiate e t))
instantiateAForm e (Pnon t) =
    (Pnon (instantiate e t))
instantiateAForm e (Uniq t) =
    (Uniq (instantiate e t))
instantiateAForm e (UniqAt t (z, i)) =
    (UniqAt
     (instantiate e t)
     ((instantiate e z), (instantiate e i)))
instantiateAForm e (Ugen t) =
    (Ugen (instantiate e t))
instantiateAForm e (UgenAt t (z, i)) =
    (UgenAt
     (instantiate e t)
     ((instantiate e z), (instantiate e i)))
instantiateAForm e (GenStV t) =
    (GenStV (instantiate e t))
instantiateAForm e (Conf t) =
    (Conf (instantiate e t))
instantiateAForm e (Auth t) =
    (Auth (instantiate e t))
instantiateAForm e (AFact pred ft) =
    (AFact pred (map (instantiate e) ft))
instantiateAForm e (Equals x y) =
    (Equals
     (instantiate e x)
     (instantiate e y))
instantiateAForm e (Component x y) =
    (Component
     (instantiate e x)
     (instantiate e y))
instantiateAForm e (Commpair (s,t) (s',t')) =
    (Commpair
     ((instantiate e s), (instantiate e t))
     ((instantiate e s'), (instantiate e t')))
instantiateAForm e (SameLocn (s,t) (s',t')) =
    (SameLocn
     ((instantiate e s), (instantiate e t))
     ((instantiate e s'), (instantiate e t')))
instantiateAForm e (StateNode (s,t)) =
    (StateNode
     ((instantiate e s), (instantiate e t)))
instantiateAForm e (Trans (s,t)) =
    (Trans
     ((instantiate e s), (instantiate e t)))
instantiateAForm e (LeadsTo (s,t) (s',t')) =
    (LeadsTo
     ((instantiate e s), (instantiate e t))
     ((instantiate e s'), (instantiate e t')))

instantiateConj :: Env -> Conj -> Conj
instantiateConj e =
    map (\(p,a) -> (p, instantiateAForm e a))

fvsAForm :: AForm -> [Term]
fvsAForm (Length _ z l) = L.nub $ sortedVarsIn z ++ sortedVarsIn l
fvsAForm (Param _ _ _ z v) = L.nub $ sortedVarsIn z ++ sortedVarsIn v
fvsAForm (Prec (z1,i1) (z2,i2)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1 ++
     sortedVarsIn z2 ++ sortedVarsIn i2

fvsAForm (Non t) = L.nub $ sortedVarsIn t
fvsAForm (Pnon t) = L.nub $ sortedVarsIn t
fvsAForm (Uniq t) = L.nub $ sortedVarsIn t
fvsAForm (Ugen t) = L.nub $ sortedVarsIn t

fvsAForm (UniqAt t (z1,i1)) =
    L.nub $ sortedVarsIn t ++ sortedVarsIn z1 ++ sortedVarsIn i1
fvsAForm (UgenAt t (z1,i1)) =
    L.nub $ sortedVarsIn t ++ sortedVarsIn z1 ++ sortedVarsIn i1

fvsAForm (GenStV t) = L.nub $ sortedVarsIn t
fvsAForm (Conf t) = L.nub $ sortedVarsIn t
fvsAForm (Auth t) = L.nub $ sortedVarsIn t

fvsAForm (Commpair (z1,i1) (z2,i2)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1 ++
     sortedVarsIn z2 ++ sortedVarsIn i2
fvsAForm (SameLocn (z1,i1) (z2,i2)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1 ++
     sortedVarsIn z2 ++ sortedVarsIn i2
fvsAForm (LeadsTo (z1,i1) (z2,i2)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1 ++
     sortedVarsIn z2 ++ sortedVarsIn i2

fvsAForm (StateNode (z1,i1)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1
fvsAForm (Trans (z1,i1)) =
    L.nub $ sortedVarsIn z1 ++ sortedVarsIn i1

fvsAForm (Equals t1 t2) = L.nub $ sortedVarsIn t1 ++ sortedVarsIn t2
fvsAForm (Component t1 t2) = L.nub $ sortedVarsIn t1 ++ sortedVarsIn t2

fvsAForm (AFact _ ts) = L.nub $ concatMap sortedVarsIn ts

fvsConj :: Conj -> [Term]
fvsConj c = L.nub $ concatMap fvsAForm $ map snd c

fvsAntec :: [AForm] -> [Term]
fvsAntec afs = L.nub $ concatMap fvsAForm afs

fvsConsq :: [([Term], [AForm])] -> [Term]
fvsConsq exs = L.nub $ concatMap (\(evs,c) -> (fvsAntec c) L.\\ evs) exs

data Rule
  = Rule { rlname :: String,    -- Name of rule
           rlgoal :: Goal,      -- Sentence
           rlcomment :: [SExpr ()] }
    deriving Show

--   data HGRule = H HornRule
--               | G GenRule

data RuleKind = NullaryRule | UnaryRule | GeneralRule

classifyRule :: Rule -> RuleKind
classifyRule r =
    let gl = rlgoal r in
    case consq gl of
      []           -> NullaryRule    -- null disjunction = false
      [([],_)]     -> UnaryRule      -- single disjunct, no existentials
      _            -> GeneralRule    -- multiple branches or any existentials

-- partition the rules given into three lists,
-- containing resp.
-- (i) those with empty (false) conclusion;
-- (ii) those with unary, existential-free conclusion;
-- (iii) those with multiple disjuncts or existential quantifiers

classifyRules :: [Rule] -> ([Rule],[Rule],[Rule])
classifyRules =
    foldl
    (\(nullSoFar,unarySoFar,genSoFar) rl ->
         case classifyRule rl of
           NullaryRule -> (rl : nullSoFar, unarySoFar, genSoFar)
           UnaryRule   -> (nullSoFar, rl : unarySoFar, genSoFar)
           GeneralRule -> (nullSoFar, unarySoFar, rl : genSoFar))
    ([],[],[])

-- Protocols

data Prot
    = Prot { pname :: !String,  -- Name of the protocol
             alg :: !String,    -- Name of the algebra
             pgen :: !Gen,      -- Initial variable generator
             psig :: !Sig,      -- The signature
             roles :: ![Role], -- Non-listener roles of a protocol
             listenerRole :: Role,
             nullaryrules :: ![Rule], -- Protocol rules: False conclusion
             unaryrules :: ![Rule],   -- Protocol rules: no branching
                                      -- or existential
             generalrules :: ![Rule], -- Protocol rules: may branch
                                      -- and introduce ex. bound vars
             userrules :: ![Rule],    -- those rules explicitly
                                      -- written by the user
             generatedrules :: ![Rule],  -- those rules created by
                                       -- the loader
             varsAllAtoms :: !Bool,   -- Are all role variables atoms?
             pcomment :: [SExpr ()] }  -- Comments from the input
    deriving Show

-- Callers should ensure every role has a distinct name.
mkProt :: String -> String -> Gen -> Sig ->
          [Role] -> Role -> [Rule] -> [Rule] -> [Rule] -> [SExpr ()] -> Prot
mkProt name alg gen sig roles lrole rules written generated comment =
    let (nrs,urs,grs) = classifyRules rules in
    Prot { pname = name, alg = alg, pgen = gen, psig = sig, roles = roles,
           listenerRole = lrole,
           nullaryrules = nrs, unaryrules = urs,  generalrules = grs,
           userrules = written, generatedrules = generated,
           pcomment = comment,
           varsAllAtoms = all roleVarsAllAtoms roles }
    where
      roleVarsAllAtoms role = all isAtom (rvars role)

rules :: Prot -> [Rule]
rules p = nullaryrules p ++ unaryrules p ++ generalrules p

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
