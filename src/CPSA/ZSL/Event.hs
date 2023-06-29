-- CPSA events and traces

module CPSA.ZSL.Event where

import CPSA.Lib.SExpr (SExpr(S, L))
import CPSA.ZSL.Term

-- Events and traces

data Event = Send Var Term | Recv Var Term deriving (Eq, Show)

type Trace  = [Event]
type Traces = [Trace]

-- Substitute a term for a variable in an event

substEvent :: Var -> Term -> Event -> Event
substEvent v t (Send c t') = Send c (substTerm t' v t)
substEvent v t (Recv c t') = Recv c (substTerm t' v t)

-- Determine whether an event is well-formed relative to a sort map

eventWf :: SortMap -> Event -> Bool
eventWf m (Send _ t) = termWf m t
eventWf m (Recv _ t) = termWf m t

-- Environments recording atom-term bindings

type Env = [(Var, Term)]

-- Perform all substitutions in an event that are possible in the
-- context of an environment

applyEnvEvent :: Env -> Event -> Event
applyEnvEvent env evt = foldl (\e x -> substEvent (fst x) (snd x) e) evt env

-- Perform all substitutions in a trace that are possible in the
-- context of an environment

applyEnvTrace :: Env -> Trace -> Trace
applyEnvTrace env = map (applyEnvEvent env)

-- Convert an event into an S-expression

sexprOfEvent :: Event -> SExpr ()
sexprOfEvent (Send c t) = L () [S () "send", S () c, sexprOfTerm t]
sexprOfEvent (Recv c t) = L () [S () "recv", S () c, sexprOfTerm t]

-- Convert a trace into an S-expression

sexprOfTrace :: Trace -> SExpr ()
sexprOfTrace trace = L () (S () "trace" : map sexprOfEvent trace)
