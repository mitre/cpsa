-- Protocol data structures

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Roletran.Protocol (
  Event (..), Trace, traceWellFormed,
  Role, mkRole, rname, rpos, rvars, rtrace, runiques, rinputs, routputs,
  Prot, mkProt, pname, ppos, roles) where

import Control.Monad (foldM)
import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Roletran.Algebra

-- Message events and traces

data Event
    = In Pos !Term !Term        -- Inbound message (channel first)
    | Out Pos !Term !Term       -- Outbound message (channel first)
      deriving Show

-- A trace is a list of events.  The terms in the trace are
-- stored in causal order.
type Trace = [Event]

-- At what position does a term originate in a trace?
originationPos :: Term -> Trace -> Maybe Int
originationPos t c =
    loop 0 c
    where
      loop _ [] = Nothing       -- Term is not carried
      loop pos (Out _ _ t' : c)
          | t `carriedBy` t' = Just pos -- Found it
          | otherwise = loop (pos + 1) c
      loop pos (In _ _ t' : c)
          | t `carriedBy` t' = Nothing -- Term does not originate
          | otherwise = loop (pos + 1) c

eventWellFormed :: VarEnv -> Event -> Maybe VarEnv
eventWellFormed env (In _ ch t) =
  doubleTermWellFormed env ch t
eventWellFormed env (Out _ ch t) =
  doubleTermWellFormed env ch t

traceWellFormed :: Trace -> Maybe VarEnv
traceWellFormed c =
  foldM eventWellFormed emptyVarEnv c

data Role = Role
    { rname :: !String,
      rpos :: !Pos,
      rvars :: !VarEnv,           -- Variables in the trace
      rtrace :: ![Event],         -- Events in causal order
      runiques :: ![(Term, Int)], -- Uniquely originating atoms and positions
      rinputs :: ![Term],         -- Sequence of inputs atoms
      routputs :: ![Term] }       -- Sequence of outputs terms
    deriving Show

{-
The translator performs various checks to ensure that each role read
is well formed.  It ensures the each term in the inputs is a basic
value.  It ensures that any basic value assumed to be uniquely
originating originates in the role's trace, and that no uniquely
originating value is in the inputs.  It ensures that no input variable
is specified as an output.  It also ensures that every variable in
terms that occur in the inputs, outputs, or are assumed to be uniquely
originating also occur in the role's trace.
-}

-- Create a role
mkRole :: MonadFail m => String -> Pos -> VarEnv -> Trace ->
          [Term] -> [Term] -> [Term] -> m Role
mkRole name pos vars trace uniques inputs outputs =
  do
    mapM_ (checkInput pos) inputs
    mapM_ (checkUniq pos inputs) uniques
    uniquesPos <- mapM (addPos pos trace) (L.nub uniques)
    mapM_ (checkOutput pos inputs) outputs
    return $ Role
      { rname = name,
        rpos = pos,
        rvars = vars,
        rtrace = trace,
        runiques = uniquesPos,
        rinputs = L.nub inputs,
        routputs = outputs
      }

checkInput :: MonadFail m => Pos -> Term -> m ()
checkInput _ input | isBasic input || isChanVar input = return ()
checkInput pos input =
    fail (shows pos $ "Input is not a basic value or a channel " ++ show input)

checkUniq :: MonadFail m => Pos -> [Term] -> Term -> m ()
checkUniq pos inputs unique
  | elem unique inputs =
      fail (shows pos $ "Uniquely originating value in input " ++ show unique)
  | otherwise = return ()

addPos :: MonadFail m => Pos -> Trace -> Term -> m (Term, Int)
addPos pos trace unique =
  case originationPos unique trace of
    Just i -> return (unique, i)
    Nothing -> fail (shows pos $ "Uniquely originating value " ++
                     show unique ++ " does not originate in trace")

checkOutput :: MonadFail m => Pos -> [Term] -> Term -> m ()
checkOutput pos inputs output
  | elem output inputs =
      fail (shows pos $ "Output contains an input value " ++ show output)
  | otherwise = return ()

-- Protocols

data Prot
    = Prot { pname :: !String,  -- Name of the protocol
             ppos :: !Pos,      -- Source position of the protocol
             roles :: ![Role] } -- Non-listener roles of a protocol
    deriving Show

-- Callers should ensure every role has a distinct name.
mkProt :: String -> Pos -> [Role] -> Prot
mkProt name pos roles =
    Prot { pname = name, ppos = pos, roles = roles }
