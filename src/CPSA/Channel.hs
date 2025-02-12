-- Channels and Channel Messages

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Channel (ChMsg (..), cmTerm, cmTerms, cmMap, cmChan,
                     cmMatch, cmMatchRename, cmUnify, cmtSubstitute,
                     cmFoldCarriedTerms,
                     CMT (..),
                     cmtMap, cmtTerms, cmtUnify, cmtTerm,
                     cmtAncestors, cmSubstitute,
                     cmtCarriedPlaces,
                    ) where

import CPSA.Algebra

-- A channel is just a variable of sort message.

-- Channel Messages

-- A channel message is either a plain message or a channel and a
-- message.

data ChMsg
  = Plain !Term                 -- Plain message
  | ChMsg !Term !Term           -- Channel and a message
  deriving (Show, Eq, Ord)

-- Get channel message term
cmTerm :: ChMsg -> Term
cmTerm (Plain t) = t
cmTerm (ChMsg _ t) = t

-- Get terms in channel message as a list
cmTerms :: ChMsg -> [Term]
cmTerms (Plain t) = [t]
cmTerms (ChMsg ch t) = [ch, t]

-- Get channel message channel
cmChan :: ChMsg -> Maybe Term
cmChan (Plain _) = Nothing
cmChan (ChMsg ch _) = Just ch

-- Map term and the channel if its there in channel message
cmMap :: (Term -> Term) -> ChMsg -> ChMsg
cmMap f (Plain  t) = Plain $ f t
cmMap f (ChMsg ch t) = ChMsg (f ch) (f t)

-- Matching

cmMatch :: ChMsg -> ChMsg -> (Gen, Env) -> [(Gen, Env)]
cmMatch (Plain t) (Plain t') ge =
  match t t' ge
cmMatch (ChMsg ch t) (ChMsg ch' t') ge =
  do
    ge <- match ch ch' ge
    match t t' ge
cmMatch _ _ _ = []

-- Match insisting on renamings
cmMatchRename :: ChMsg -> ChMsg -> (Gen, Env) -> [(Gen, Env)]
cmMatchRename (Plain t) (Plain t') ge =
    matchRename t t' ge
cmMatchRename (ChMsg ch t) (ChMsg ch' t') ge =
    do
      ge <- matchRename ch ch' ge
      matchRename t t' ge
cmMatchRename _ _ _ = [] 

-- Unification

cmUnify :: ChMsg -> ChMsg -> (Gen, Subst) -> [(Gen, Subst)]
cmUnify (Plain t) (Plain t') gs =
  unify t t' gs
cmUnify (ChMsg ch t) (ChMsg ch' t') gs =
  do
    gs <- unify ch ch' gs
    unify t t' gs
cmUnify _ _ _ = []

cmSubstitute :: Subst -> ChMsg -> ChMsg
cmSubstitute subst t = cmMap (substitute subst) t

cmFoldCarriedTerms :: (a -> CMT -> a) -> a -> ChMsg -> a
cmFoldCarriedTerms f acc cm@(ChMsg _ t) =
  foldCarriedTerms g (f acc (CM cm)) t
  where
    g acc t = f acc (TM t)
cmFoldCarriedTerms f acc (Plain t) =
  foldCarriedTerms g acc t
  where
    g acc t = f acc (TM t)

-- Channel messages or internal terms

data CMT
  = TM Term
  | CM ChMsg
  deriving (Show, Eq, Ord)

-- Map term and the channel if its there in channel message
cmtMap :: (Term -> Term) -> CMT -> CMT
cmtMap f (CM t) = CM $ cmMap f t
cmtMap f (TM t) = TM $ f t

cmtTerms :: CMT -> [Term]
cmtTerms (CM cm) = cmTerms cm
cmtTerms (TM t) = [t]

cmtUnify :: CMT -> CMT -> (Gen, Subst) -> [(Gen, Subst)]
cmtUnify (CM t) (CM t') gs = cmUnify t t' gs
cmtUnify (TM t) (TM t') gs = unify t t' gs
cmtUnify _ _ _ = []

cmtTerm :: CMT -> Term
cmtTerm (CM cm) = cmTerm cm
cmtTerm (TM t) = t

-- Carried places

cmtCarriedPlaces :: CMT -> ChMsg -> [Place]
cmtCarriedPlaces (TM ct) (Plain t) =
  map (prefix 0) (carriedPlaces ct t)
cmtCarriedPlaces (TM ct) (ChMsg _ t) =
  map (prefix 1) (carriedPlaces ct t)
cmtCarriedPlaces (CM ct) cm
  | ct == cm = [Place []]
cmtCarriedPlaces _ _ = []

prefix :: Int -> Place -> Place
prefix n (Place p) = Place (n : p)

cmtAncestors :: ChMsg -> Place -> [CMT]
cmtAncestors _ (Place []) = []
cmtAncestors cm@(Plain t) (Place (0 : path)) =
  CM cm : map TM (ancestors t (Place path))
cmtAncestors cm@(ChMsg _ t) (Place (1 : path)) =
  CM cm : map TM (ancestors t (Place path))
cmtAncestors _ _ = error "Channel.cmtAncestors: Bad path to term"

{-
cmAncestors :: ChMsg -> Place -> [CMT]
cmAncestors ::
cmAncestors _ (Place []) = []
cmAncestors cm@(Plain t) (Place (0 : path)) =
  cm : map Plain (ancestors t (Place path))
cmAncestors cm@(ChMsg _ t) (Place (1 : path)) =
  cm : map Plain (ancestors t (Place path))
cmAncestors _ _ = error "Channel.cmAncestors: Bad path to term"
-}

cmtSubstitute :: Subst -> CMT -> CMT
cmtSubstitute subst t = cmtMap (substitute subst) t
