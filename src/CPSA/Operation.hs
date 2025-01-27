-- The operation datastructure

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Operation (Sid, Node, Pair,
                       Cause (..), Direction (..),
                       Method (..), Operation (..),
                       getStrandMap, addStrandMap) where

import Data.Set (Set)
import CPSA.Algebra (Term, Subst)
import CPSA.Channel (CMT)

type Sid = Int                  -- Strand Identifier

-- A node is composed of two integers, a strand identifier and a
-- position.  The position identifies an event in the strand's trace.
-- The second integer must be non-negative and less than the strand's
-- height

type Node = (Sid, Int)

-- A pair gives an ordering of two nodes, meaning the first node is
-- before the second one.

type Pair = (Node, Node)

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
    | Contracted [Sid] Subst Cause
    | Displaced [Sid] Int Int String Int Cause
    | AddedStrand [Sid] String Int Cause
    | AddedListener [Sid] Term Cause
    | AddedAbsence [Sid] Term Term Cause
    | Generalized [Sid] Method
    | Collapsed [Sid] Int Int
    | AppliedRules [Sid] 
      deriving Show


getStrandMap :: Operation -> [Sid]
getStrandMap New = []
getStrandMap (Contracted sm _ _) = sm
getStrandMap (Displaced sm _ _ _ _ _) = sm
getStrandMap (AddedStrand sm _ _ _) = sm
getStrandMap (AddedListener sm _ _) = sm
getStrandMap (AddedAbsence sm _ _ _) = sm
getStrandMap (Generalized sm _) = sm
getStrandMap (Collapsed sm _ _) = sm
getStrandMap (AppliedRules sm) = sm

addStrandMap :: [Sid] -> Operation -> Operation
addStrandMap _ New = New
addStrandMap sm (Contracted _ s c) = Contracted sm s c
addStrandMap sm (Displaced _ n1 n2 str n3 c) =
    Displaced sm n1 n2 str n3 c
addStrandMap sm (AddedStrand _ str n c) = AddedStrand sm str n c
addStrandMap sm (AddedListener _ t c) = AddedListener sm t c
addStrandMap sm (AddedAbsence _ t1 t2 c) = AddedAbsence sm t1 t2 c
addStrandMap sm (Generalized _ m) = Generalized sm m
addStrandMap sm (Collapsed _ n1 n2) = Collapsed sm n1 n2
addStrandMap sm (AppliedRules _) = AppliedRules sm
