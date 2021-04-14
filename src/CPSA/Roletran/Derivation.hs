-- Constructs a procedure from a role using derivations

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

{-# LANGUAGE CPP #-}

#if !(MIN_VERSION_base(4,13,0))
#define MonadFail Monad
#endif

module CPSA.Roletran.Derivation (derive) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import CPSA.Lib.SExpr (Pos)
import CPSA.Roletran.Algebra
import CPSA.Roletran.Protocol
import CPSA.Roletran.Emitter
import CPSA.Roletran.Displayer (displayTerm)

-- At this stage, program variables are represented as integers.  We
-- call this representation of a program variable a variable index.

-- The compile time store is a map from terms to variable indices.  At
-- runtime, the variable will be bound to a data object that is
-- represented by the term.
type CompStore = Map Term Vari

-- Entry point for compilation by derivation
derive :: MonadFail m => Role -> m Proc
derive r =
  do
    -- Construct the parameter bindings.
    let (fresh, bindings, ins) = bindInputs (rinputs r)
    -- Ensure inputs are receivable
    mapM_ (checkInput (rpos r)) (reverse bindings)
    -- Construct the statements from the inputs
    preamble <- deriveInputs r fresh (reverse bindings)
    -- Construct a list of the return types.
    let outs = map kind (routputs r)
    -- Construct the statements that form the body of the procedure.
    stmts <- deriveStmts r preamble
    return $ mkProc
      (rname r)
      (rpos r)
      (reverse ins)
      outs
      (reverse stmts)

-- Allocate variable indices to inputs and create procedure
-- declarations.
bindInputs :: [Term] -> (Vari, [(Term, Vari)], [Decl])
bindInputs ts =
  foldl f (0, [], []) ts
  where
    f (fresh, binding, ins) t =
      (fresh + 1, (t, fresh) : binding, (fresh, kind t) : ins)

-- The state association with compilation
type State = (Vari, CompStore, [Stmt])

-- Accessors for the state

-- The first component is the next available variable index.
freshVar :: State -> Vari
freshVar (fresh, _, _) = fresh

-- The second component is the compile time store.
compStore :: State -> CompStore
compStore (_, cs, _) = cs

-- The third component is the current list of statements.
statements :: State -> [Stmt]
statements (_, _, stmts) = stmts

-- Construct statements for an input.
checkInput :: MonadFail m => Pos -> (Term, Vari) -> m ()
checkInput pos (t, _) =
  case receivable t of
    Nothing ->                  -- t is receivable.
      return ()
    Just t ->                   -- t is the offending term
      fail (shows pos ("Input not receivable " ++ show (displayTerm t)))

-- Compile the inputs.
deriveInputs :: MonadFail m => Role -> Vari -> [(Term, Vari)] -> m State
deriveInputs r fresh ts =
  reduce (rpos r) (fresh, M.empty, []) ts

-- Compile the trace and the outputs.
deriveStmts :: MonadFail m => Role -> State -> m [Stmt]
deriveStmts r st =
  do
    st <- foldM (deriveEvent (runiques r))
                st
                (zip (rtrace r) [0..])
    deriveOutputs st r

-- Compile an event.
deriveEvent :: MonadFail m => [(Term, Int)] ->
               State -> (Event, Int) -> m State
-- Compile a send event.  Variable i holds the position of the event
-- in the trace.  It used to determine when to bind uniques to nonces.
deriveEvent uniques st ((Out pos ch t), i) =
  case receivable t of
    Nothing ->                  -- t is receivable.
      do
        -- Create uniques and synthesize the channel
        (st, chan) <- build pos (deriveUniques uniques i (sendCmt pos st)) ch
        -- Synthesize the message
        (st, v) <- build pos st t
        return (
          freshVar st,
          compStore st,
          Send chan (v, kind t) : statements st)
    Just t ->                   -- t is the offending term
      fail (shows pos ("Message not receivable " ++ show (displayTerm t)))

-- Compile a recv event.
deriveEvent _ st ((In pos ch t), _) =
  case receivable t of
    Nothing ->                  -- t is receivable.
      do
        -- Synthesize the channel.
        (st, chan) <- build pos (recvCmt pos st) ch
        let (fresh, cs, stmts) = st
        let recv = Recv (fresh, kind t) chan
        let st' = (fresh + 1, cs, recv : stmts)
        -- Associate fresh with the received message.
        reduce pos st' [(t, fresh)]
    Just t ->                   -- t is the offending term
      fail (shows pos ("Message not receivable " ++ show (displayTerm t)))

-- Comments for events

sendCmt :: Pos -> State -> State
sendCmt pos (fresh, cs, stmts) =
  (fresh, cs, Comment ("Send (" ++ displayPos pos ++ ")") : stmts)

recvCmt :: Pos -> State -> State
recvCmt pos (fresh, cs, stmts) =
  (fresh, cs, Comment ("Recv (" ++ displayPos pos ++ ")") : stmts)

-- Add uniques as appropriate.
deriveUniques :: [(Term, Int)] -> Int -> State -> State
deriveUniques uniques i st =
  foldl f st uniques
  where
    f st@(fresh, cs, stmts) (t, j)
      | i == j = (fresh + 1,
                  M.insert t fresh cs, -- Bind fresh to a nonce.
                  Bind (fresh, kind t) (Nonce (kind t)) : stmts)
      | otherwise = st

-- Synthesize a term and fail when it can't be built.
build :: MonadFail m => Pos -> State -> Term -> m (State, Vari)
build pos st t =
  case synth st t of
    Nothing -> fail (shows pos ("Cannot build " ++ show (displayTerm t)))
    Just result -> return result

-- Synthesize a term and return Nothing when it can't be synthesized.
synth :: State -> Term -> Maybe (State, Vari)
synth st t =
  case M.lookup t (compStore st) of
    Just v -> Just (st, v)      -- Apply the Mem rule
    Nothing ->
      case t of
        Pr x y -> synthPair st t x y -- Apply the Pair rule
        En x y -> synthEncr st t x y -- Apply the Encr rule
        Hsh x -> synthHash st t x    -- Apply the Hash rule
        Tag s -> synthTag st t s     -- Apply the Tag rule
        _ -> Nothing

synthPair :: State -> Term -> Term -> Term -> Maybe (State, Vari)
synthPair st t x y =
  do
    (st, v) <- synth st x
    ((fresh, cs, stmts), u) <- synth st y
    return (
      (fresh + 1,
       M.insert t fresh cs,     -- Bind fresh to the pair t.
       Bind (fresh, kind t) (Pair (v, kind x) (u, kind y)) : stmts),
      fresh)

synthEncr :: State -> Term -> Term -> Term -> Maybe (State, Vari)
synthEncr st t x y =
  do
    (st, v) <- synth st x
    ((fresh, cs, stmts), u) <- synth st y
    return (
      (fresh + 1,
       M.insert t fresh cs,     -- Bind fresh to the encryption t.
       Bind (fresh, kind t) (Encr (v, kind x) (u, kind y)) : stmts),
      fresh)

synthHash :: State -> Term -> Term -> Maybe (State, Vari)
synthHash st t x  =
  do
    ((fresh, cs, stmts), v) <- synth st x
    return (
      (fresh + 1,
       M.insert t fresh cs,     -- Bind fresh to the hash t.
       Bind (fresh, kind t) (Hash (v, kind x)) : stmts),
      fresh)

synthTag :: State -> Term -> String -> Maybe (State, Vari)
synthTag (fresh, cs, stmts) t s  =
  return (
    (fresh + 1,
     M.insert t fresh cs,       -- Bind fresh to the tag.
     Bind (fresh, kind t) (Tagg s) : stmts),
    fresh)

-- Reduce a received term.  This is by far the trickiest code.  The
-- reason is there is a loop that repeats as long as progress is being
-- made.
reduce :: MonadFail m => Pos -> State -> [(Term, Vari)] -> m State
reduce pos st cs =
  loop pos st False cs []

-- The loop parameters are
-- pos:   the position of the received term in the source file
-- st:    the current state
-- more:  a boolean that is true when there is more to be done
-- recvd: unprocessed received terms and their variable indices
-- todo:  received terms and their variables put off for later processing
loop :: MonadFail m => Pos -> State -> Bool ->
        [(Term, Vari)] -> [(Term, Vari)] -> m State
loop _ st _ [] [] = return st
loop pos st True [] todo =      -- More todo
  loop pos st False todo []
loop pos _ False [] (_ : _) =   -- No progress can be made
  fail (shows pos "Received term cannot be fully destructured")
loop pos st more ((t, v) : recvd) todo =
  case t of                     -- Dispatch on the form of the term
    Pr x y -> loopPair pos st recvd todo t v x y
    En x y -> loopEncr pos st more recvd todo t v x y
    Hsh _ -> loopHash pos st more recvd todo t v
    _ -> loopOther pos st more recvd todo t v

-- Reduce a pair.  Adds two instructions and allocates two variables.
-- Applies the Frst and Scnd rules
loopPair :: MonadFail m => Pos -> State ->
            [(Term, Vari)] -> [(Term, Vari)] ->
            Term -> Vari -> Term -> Term -> m State
loopPair pos (fresh, cs, stmts) recvd todo t v x y =
  do
    let stmtX = Bind (fresh, kind x) (Frst (kind x) v)
    let stmtY = Bind (fresh + 1, kind y) (Scnd (kind y) v)
    let st = (
          fresh + 2,
          M.insert t v cs,      -- Add pair to the compile time store
          stmtY : stmtX : stmts)
    loop pos st True recvd ((x, fresh) : (y, fresh + 1) : todo)

-- Reduce an encryption.  If the inverse key can be synthesized, it
-- adds two instructions and allocates two variables.
-- Applies the Decr rule
loopEncr :: MonadFail m => Pos -> State -> Bool ->
            [(Term, Vari)] -> [(Term, Vari)] ->
            Term -> Vari -> Term -> Term -> m State
loopEncr pos st more recvd todo t v x y =
  case synth st (inv y) of
    Nothing ->                  -- Can't synthesize key -- no progress
      loop pos st more recvd ((t, v) : todo)
    Just ((fresh, cs, stmts), k) ->
      do
        let stmt = Bind (fresh, kind x) (Decr (kind x) v (k, kind y))
        let st = (
              fresh + 1,
              M.insert t v cs, -- Add encryption to the compile time store
              stmt : stmts)
        loop pos st True recvd ((x, fresh) : todo)

loopHash :: MonadFail m => Pos -> State -> Bool ->
            [(Term, Vari)] -> [(Term, Vari)] ->
            Term -> Vari -> m State
loopHash pos st more recvd todo t v =
  case synth st t of
    Nothing ->                 -- Can't synthesize hash -- no progress
      loop pos st more recvd ((t, v) : todo)
    Just ((fresh, cs, stmts), h) ->
      do
        let stmt = Same (kind t) v h
        let st = (fresh, cs, stmt : stmts)
        loop pos st True recvd todo

-- Reduce terms other than pairs, encryptions, and hashes.
loopOther :: MonadFail m => Pos -> State -> Bool ->
            [(Term, Vari)] -> [(Term, Vari)] ->
            Term -> Vari -> m State
loopOther pos st@(fresh, cs, stmts) more recvd todo t v =
  case synth st t of
    Nothing ->                  -- Add new term
      loop pos (fresh, M.insert t v cs, stmts) True recvd todo
    Just ((fresh, cs, stmts), h) ->
      do                        -- Otherwise, check sameness
        let stmt = Same (kind t) v h
        let st = (fresh, cs, stmt : stmts)
        loop pos st more recvd todo

deriveOutputs :: MonadFail m => State -> Role -> m [Stmt]
deriveOutputs st r =
  do
    (st, vs) <-
      foldM (deriveOutput $ rpos r) (st, []) (routputs r)
    return $ Return (reverse vs) : statements st

-- Synthesize each output and add it to the list
deriveOutput :: MonadFail m => Pos -> (State, [Vari]) ->
                Term -> m (State, [Vari])
deriveOutput pos (st, vs) t =
  case receivable t of
    Nothing ->                  -- t is receivable.
      do
        (st, v) <- build pos st t
        return (st, v : vs)
    Just t ->                   -- t is the offending term
      fail (shows pos ("Message not receivable " ++ show (displayTerm t)))
