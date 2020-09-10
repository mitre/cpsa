-- CPSA4 message terms and their sorts for cpsa4roletran
--
-- This module implements CPSA message algebra terms.  In CPSA4, the
-- message algebra is order-sorted.  The sorts are text, data, name,
-- skey, akey, mesg, and chan.  The sorts text, data, name, skey, and
-- akey are a subsort of mesg.  The compiler makes no use of the
-- subsort relation, so it implements the algebra as if it were
-- many-sorted.  (The runtime system makes use of the subsort
-- relation.)
--
-- For output, there is a type for each sort, except that there
-- are two types for sort akey, Akey and Ikey.  Following the
-- convention on asymmetric key pairs, an asymmetric key is assumed to
-- be public, and therefore has type Akey, if it has the form t or
-- (pubk n), and private, and therefore has type Ikey, if it has the
-- form (invk k) or (privk n).

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Roletran.Algebra (
  Sort(..), Var, Term(..), Skey(..), Akey(..),
  sort, inv, isBasic, isMesgVar, isChanVar, VarEnv,
  emptyVarEnv, doubleTermWellFormed, carriedBy, receivable) where

import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)

-- The Rust type associated with a variable or a term.  We call it the
-- sort because type is a Haskell keyword.  A variable is never of
-- sort Ikey.
data Sort
  = Text                        -- Plaintext
  | Data                        -- Data
  | Name                        -- Name
  | Skey                        -- Symmetric key
  | Akey                        -- Public asymmetric key
  | Ikey                        -- Private asymmetric key
  | Mesg                        -- Message -- top sort for terms
  | Chan                        -- Channels -- not allowed
  deriving (Show, Eq)           -- in terms in events

type Var = String

-- A term.  Note that not all terms are well formed.  See below for a
-- function that checks for well formedness.
data Term
  = Txt Var              -- Text variable
  | Dta Var              -- Data variable
  | Nam Var              -- Name variable
  | Sky Skey             -- Symmetric key
  | Aky Akey             -- Asymmetric key
  | Msg Var              -- Message variable
  | Tag String           -- A message tag
  | Pr Term Term         -- A pair of terms,
  | En Term Term         -- Encryption of a plain text term with a key
  | Hsh Term             -- Hash of some term
  | Chn Var              -- Channel variable
  deriving (Show, Eq, Ord)

-- Symmetric keys
data Skey
  = SVar Var       -- Symmetric key variable
  | Ltk Var Var    -- A long term key associated with two name variables
  deriving (Show, Eq, Ord)

-- Asymmetric keys
data Akey
  = AVar Var                  -- Asymmetric key variable
  | Inv Var                   -- Inverse of an asymmetric key variable
  | Pubk Var                  -- Public key of a name variable
  | Pubk2 String Var          -- Tagged public key of a name variable
  | Privk Var                 -- Private key of a name variable
  | Privk2 String Var         -- Tagged private key of a name variable
  deriving (Show, Eq, Ord)

-- Return the sort of a term.
sort :: Term -> Sort
sort (Txt _) = Text
sort (Dta _) = Data
sort (Nam _) = Name
sort (Sky _) = Skey
sort (Aky k) =
  case k of
    AVar _ -> Akey
    Inv _ -> Ikey
    Pubk _ -> Akey
    Pubk2 _ _ -> Akey
    Privk _ -> Ikey
    Privk2 _ _ -> Ikey
sort (Msg _) = Mesg
sort (Tag _) = Mesg
sort (Pr _ _) = Mesg
sort (En _ _) = Mesg
sort (Hsh _) = Mesg
sort (Chn _) = Chan

-- Inverse key
inv :: Term -> Term
inv (Aky k) =
  case k of
    AVar v -> Aky (Inv v)
    Inv v -> Aky (AVar v)
    Pubk v -> Aky (Privk v)
    Pubk2 c v -> Aky (Privk2 c v)
    Privk v -> Aky (Pubk v)
    Privk2 c v -> Aky (Pubk2 c v)
inv t = t

-- Is term a CPSA basic value?
isBasic :: Term -> Bool
isBasic (Txt _) = True
isBasic (Dta _) = True
isBasic (Nam _) = True
isBasic (Sky _) = True
isBasic (Aky _) = True
isBasic _ = False

-- Is term a CPSA message variable?
isMesgVar :: Term -> Bool
isMesgVar (Msg _) = True
isMesgVar _ = False

-- Is term a CPSA channel variable?
isChanVar :: Term -> Bool
isChanVar (Chn _) = True
isChanVar _ = False

type VarEnv = Map Var Sort

emptyVarEnv :: VarEnv
emptyVarEnv = M.empty

termWellFormed :: VarEnv -> Term -> Maybe VarEnv
termWellFormed env t@(Txt x) =
    extendVarEnv env x (sort t) -- Text variable
termWellFormed env t@(Dta x) =
    extendVarEnv env x (sort t) -- Data variable
termWellFormed env t@(Nam x) =
    extendVarEnv env x (sort t) -- Name variable
termWellFormed env t@(Sky (SVar x)) =
    extendVarEnv env x (sort t) -- Symmetric key variable
termWellFormed env (Sky (Ltk x y)) =
    -- Long term shared symmetric key
    doubleTermWellFormed env (Nam x) (Nam y)
termWellFormed env (Aky t) =    -- Asymmetric key terms
    case t of
      AVar x -> extendVarEnv env x Akey
      Inv x -> extendVarEnv env x Akey
      Pubk x -> extendVarEnv env x Name
      Pubk2 _ x -> extendVarEnv env x Name
      Privk x -> extendVarEnv env x Name
      Privk2 _ x -> extendVarEnv env x Name
termWellFormed env t@(Msg x) =
    extendVarEnv env x (sort t) -- Mesg variable
termWellFormed env (Tag _) =
    Just env                    -- Tags
termWellFormed env (Pr x y) =
    doubleTermWellFormed env x y -- Pairing
termWellFormed env (En x y) =
    doubleTermWellFormed env x y -- Encryption
termWellFormed env (Hsh t) =
    termWellFormed env t        -- Hashing
termWellFormed env t@(Chn x) =
    extendVarEnv env x (sort t) -- Channel variable

-- Extend when sorts agree
extendVarEnv :: VarEnv -> Var -> Sort -> Maybe VarEnv
extendVarEnv env x s =
    case M.lookup x env of
      Nothing -> Just $ M.insert x s env
      Just s' -> if s == s' then Just env else Nothing

doubleTermWellFormed :: VarEnv -> Term -> Term -> Maybe VarEnv
doubleTermWellFormed env x y =
    do
      env <- termWellFormed env x
      termWellFormed env y

-- Is a term carried by another term?
carriedBy :: Term -> Term -> Bool
carriedBy t t' =
    t == t' ||
      case t' of
        Pr x y -> carriedBy t x || carriedBy t y
        En x _ -> carriedBy t x
        _ -> False

-- Check to make sure a message is receivable.  If not, return
-- the offending term.
--
-- A message t is receivable iff
--
-- 1. t contains no occurrence of an encryption in the key of an
--    encryption, and
--
-- 2. t contains no occurrence of an encryption within a hash.

receivable :: Term -> Maybe Term
receivable (Pr x y) =
  case receivable x of
    Just t -> Just t
    Nothing -> receivable y
receivable (En x y) =
  case receivable x of
    Just t -> Just t
    Nothing -> findEnc y
receivable (Hsh x) = findEnc x
receivable _ = Nothing

findEnc :: Term -> Maybe Term
findEnc (Pr x y) =
  case findEnc x of
    Just t -> Just t
    Nothing -> findEnc y
findEnc t@(En _ _) = Just t
findEnc (Hsh x) = findEnc x
findEnc _ = Nothing
