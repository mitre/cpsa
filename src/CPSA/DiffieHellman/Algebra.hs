-- Diffie-Hellman Algebra implementation

-- FIX ME!!!
-- This module is a version of Diffie-Hellman in which exponents form
-- an Abelian group.  There are many issues to be resolved before this
-- version of Diffie-Hellman can be used.

-- FIX ME!!
-- Add hash

-- The module implements a many-sorted algebra, but is used as an
-- order-sorted algebra.  It exports a name, and the origin used to
-- generate variables.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

{-# LANGUAGE MultiParamTypeClasses #-}

module CPSA.DiffieHellman.Algebra (name, origin) where

import Control.Monad (foldM)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Char (isDigit)
import qualified CPSA.Lib.CPSA as C
import CPSA.Lib.CPSA (SExpr(..), Pos, annotation)

{-- Debugging support
import System.IO.Unsafe

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x

zn :: Show a => a -> Maybe b -> Maybe b
zn x Nothing = z x Nothing
zn _ y = y

zf :: Show a => a -> Bool -> Bool
zf x False = z x False
zf _ y = y

zt :: Show a => a -> Bool -> Bool
zt x True = z x True
zt _ y = y
--}

{- Export iUnify and iMatch for GHCi for debugging

For this to work, you must install the package bytestring-handle from
Hackage and tell GHCi that it is not hidden on the command line or
within GHCi with:

:set -package bytestring-handle

-}

{--
import System.IO (Handle)
import Data.ByteString.Lazy.Char8 (pack)
import Data.ByteString.Handle
import Control.Exception (try)
import System.IO.Unsafe

stringHandle :: String -> IO Handle
stringHandle s = readHandle False (pack s)

stringPosHandle :: String -> IO C.PosHandle
stringPosHandle s =
    do
      h <- stringHandle s
      C.posHandle "" h

stringLoad :: String -> IO [SExpr Pos]
stringLoad s =
    do
      h <- stringPosHandle s
      loop h []
    where
      loop h xs =
          do
            x <- C.load h
            case x of
              Nothing ->
                return $ reverse xs
              Just x ->
                loop h (x : xs)

sLoad :: String -> [[SExpr Pos]]
sLoad s =
    [unsafePerformIO $ stringLoad s]

-- Test unification

iUnify :: String -> String -> String -> [Subst]
iUnify vars t t' =
    iRun unify emptySubst vars t t'

-- Test matching

iMatch :: String -> String -> String -> [Env]
iMatch vars t t' =
    iRun match emptyEnv vars t t'

iRun :: (Term -> Term -> (Gen, a) -> [(Gen, a)]) -> a ->
        String -> String -> String -> [a]
iRun f mt vars t t' =
    do
      vars <- sLoad vars
      [t] <- sLoad t
      [t'] <- sLoad t'
      (gen, vars) <- loadVars origin vars
      t <- loadTerm vars t
      t' <- loadTerm vars t'
      (_, a) <- f t t' (gen, mt)
      return a

gRun :: Gen -> Term -> a -> a
gRun (Gen n) t a =
    foldVars f a t
    where
      f a t =
          case varId t of
            Id (m, _) | m >= n -> error ("Bad gen " ++ show n)
            _ -> a

gMatch :: Term -> Term -> GenEnv -> [GenEnv]
gMatch t t' r@(g, _) = gRun g t' (match t t' r)

gUnify :: Term -> Term -> GenSubst -> [GenSubst]
gUnify t t' r@(g, _) = gRun g (F Cat [t, t']) (unify t t' r)
--}

name :: String
name = "diffie-hellman"

-- An identifier

newtype Id = Id (Integer, String) deriving Show

-- The integer distinguishes an identifier, the string is for printing.

instance Eq Id where
  (Id (x, _)) == (Id (x', _)) = x == x'

instance Ord Id where
  compare (Id (x, _)) (Id (x', _)) = compare x x'

idName :: Id -> String
idName (Id (_, name)) = name

-- Counter used for generating fresh identifiers.

newtype Gen = Gen (Integer) deriving Show

origin :: Gen
origin = Gen (0)

freshId :: Gen -> String -> (Gen, Id)
freshId (Gen (i)) name = (Gen (i + 1), Id (i, name))

cloneId :: Gen -> Id -> (Gen, Id)
cloneId gen x = freshId gen (idName x)

{--
mash :: Gen -> Gen -> Gen
mash (Gen i) (Gen j) = Gen (max i j)
-}

-- A term in an Abelian group is a map from identifiers to pairs of
-- bools and non-zero integers.  The boolean is true if the variable
-- is a basis element.

type Coef = Int

type Desc = (Bool, Coef)

type Group = Map Id Desc

isGroupVar :: Group -> Bool
isGroupVar t =
  M.size t == 1 && snd (head (M.elems t)) == 1

isBasisVar :: Group -> Bool
isBasisVar t =
  M.size t == 1 && head (M.elems t) == (True, 1)

-- Assumes isGroupVar t == True or isBasisVar t == True!
getGroupVar :: Group -> Id
getGroupVar x = head $ M.keys x

-- Create group var as a basis element if be is true
groupVar :: Bool -> Id -> Term
groupVar be x = G $ M.singleton x (be, 1)

dMapCoef :: (Coef -> Coef) -> Desc -> Desc
dMapCoef f (be, c) = (be, f c)

invert :: Group -> Group
invert t = M.map (dMapCoef negate) t

expg :: Group -> Int -> Group
expg _ 0 = M.empty
expg t 1 = t
expg t n = M.map (dMapCoef (n *)) t

mul :: Group -> Group -> Group
mul t t' =
  M.foldrWithKey f t' t         -- Fold over the mappings in t
  where
    f x c t =                   -- Alter the mapping of
      M.alter (g c) x t         -- variable x in t
    g c Nothing =               -- Variable x not currently mapped
      Just c                    -- so add a mapping
    g (b, c) (Just (b', c'))    -- Variable x maps to c'
      | b /= b' = error "Algebra.mul: sort mismatch"
      | c + c' == 0 = Nothing          -- Delete the mapping
      | otherwise = Just $ (b, c + c') -- Adjust the mapping

-- Why not replace M.assocs with M.toList elsewhere?

type Maplet = (Id, Desc)

mMapCoef :: (Coef -> Coef) -> Maplet -> Maplet
mMapCoef f (x, (be, c)) = (x, (be, f c))

mInverse :: [Maplet] -> [Maplet]
mInverse maplets = map (mMapCoef negate) maplets

{--
mlGrp :: Maplet -> Group
mlGrp (x, d) = M.singleton x d
-}

isMapletNonzero :: Maplet -> Bool
isMapletNonzero (_, (_, c)) = c /= 0

group :: [Maplet] -> Group
group maplets =
  M.fromList $ filter isMapletNonzero maplets

-- Function symbols--see foldVar to see the arity of each symbol.
data Symbol
    = Text                      -- Text atom
    | Data                      -- Another text-like atom
    | Name                      -- Principal atom
    | Skey                      -- Symmetric key atom
    | Base                      -- Base of an exponentiated atom
    | Ltk                       -- Long term shared symmetric key
    | Akey                      -- Asymmetric key atom
    | Invk                      -- Inverse of asymmetric key
    | Pubk                      -- Public asymmetric key of a principal
    | Genr                      -- The generator constant for the group
    | Exp                       -- Exponentiation function symbol
    | Cat                       -- Term concatenation
    | Enc                       -- Encryption
      deriving (Show, Eq, Ord, Enum, Bounded)

-- A Basic Crypto Algebra Term

data Term
    = I !Id
    | C !String
    | F !Symbol ![Term]
    | G !Group                  -- An exponent, an Abelian group
      deriving Show

equalTerm :: Term -> Term -> Bool
equalTerm (I x) (I y) = x == y
equalTerm (C c) (C c') = c == c'
equalTerm (F Invk [F Invk [t]]) t' = equalTerm t t'
equalTerm t (F Invk [F Invk [t']]) = equalTerm t t'
equalTerm (F Exp [t0, G t1]) t' | M.null t1 = equalTerm t0 t'
equalTerm t (F Exp [t0, G t1]) | M.null t1 = equalTerm t t0
equalTerm (F Exp [F Exp [t, G t0], G t1]) t' =
  equalTerm (F Exp [t, G (mul t0 t1)]) t'
equalTerm t (F Exp [F Exp [t', G t0], G t1])  =
  equalTerm t (F Exp [t', G (mul t0 t1)])
equalTerm (F s u) (F s' u') =
  s == s' && equalTermLists u u'
equalTerm (G t) (G t') = t == t'
equalTerm _ _ = False

equalTermLists :: [Term] -> [Term] -> Bool
equalTermLists [] [] = True
equalTermLists (t : u) (t' : u') =
  equalTerm t t' && equalTermLists u u'
equalTermLists _ _ = False

instance Eq Term where
  (==) = equalTerm

-- Term comparison respecting the axiom

compareTerm :: Term -> Term -> Ordering
compareTerm (I x) (I y) = compare x y
compareTerm (C c) (C c') = compare c c'
compareTerm (F Invk [F Invk [t]]) t' = compareTerm t t'
compareTerm t (F Invk [F Invk [t']]) = compareTerm t t'
compareTerm (F Exp [t0, G t1]) t' | M.null t1 = compareTerm t0 t'
compareTerm t (F Exp [t0, G t1]) | M.null t1 = compareTerm t t0
compareTerm (F Exp [F Exp [t, G t0], G t1]) t' =
  compareTerm (F Exp [t, G (mul t0 t1)]) t'
compareTerm t (F Exp [F Exp [t', G t0], G t1])  =
  compareTerm t (F Exp [t', G (mul t0 t1)])
compareTerm (F s u) (F s' u') =
  case compare s s' of
    EQ -> compareTermLists u u'
    o -> o
compareTerm (G t) (G t') = compare t t'
compareTerm (I _) (C _) = LT
compareTerm (C _) (I _) = GT
compareTerm (I _) (F _ _) = LT
compareTerm (F _ _) (I _) = GT
compareTerm (I _) (G _) = LT
compareTerm (G _) (I _) = GT
compareTerm (C _) (F _ _) = LT
compareTerm (F _ _) (C _) = GT
compareTerm (C _) (G _) = LT
compareTerm (G _) (C _) = GT
compareTerm (F _ _) (G _) = LT
compareTerm (G _) (F _ _) = GT

compareTermLists :: [Term] -> [Term] -> Ordering
compareTermLists [] [] = EQ
compareTermLists (t : u) (t' : u') =
  case compareTerm t t' of
    EQ -> compareTermLists u u'
    o -> o
compareTermLists [] _ = LT
compareTermLists _ [] = GT

instance Ord Term where
  compare = compareTerm

-- Basic terms are introduced by defining a function used to decide if
-- a term is well-formed.  The context of an occurrence of an identifier
-- determines its sort.  A term that contains just an identifier and its
-- sort information is called a variable.  The sort of a variable is
-- one of mesg, text, data, name, skey, akey, base, or expn.

-- Terms that represent variables.
isVar :: Term -> Bool
isVar (I _) = True           -- Sort: mesg
isVar (F s [I _]) =
  -- Sorts: text, data, name, skey, and akey
  s == Text || s == Data || s == Name || s == Skey || s == Akey || s == Base
isVar (G x) = isGroupVar x
isVar _ = False

-- Extract the identifier from a variable
varId :: Term -> Id
varId (I x) = x
varId (F Text [I x]) = x
varId (F Data [I x]) = x
varId (F Name [I x]) = x
varId (F Skey [I x]) = x
varId (F Akey [I x]) = x
varId (F Base [I x]) = x
varId (G x) | isGroupVar x = getGroupVar x
varId _ = error "Algebra.varId: term not a variable with its sort"

isAcquiredVar :: Term -> Bool
isAcquiredVar (I _) = True
isAcquiredVar (F Base [I _]) = True
isAcquiredVar _ = False

-- A list of terms are well-formed if each one has the correct
-- structure and every occurrence of an identifier in a term has the
-- same sort.  Variable environments are used to check the sort
-- condition.  It maps an identifier to a variable that contains the
-- identifier.

-- termsWellFormed u ensures all terms in u use each identifier at the
-- same sort, and makes sure every term has the correct structure.
termsWellFormed :: [Term] -> Bool
termsWellFormed u =
  loop emptyVarEnv u
  where
    loop _ [] = True
    loop env (t : u) =
      case termWellFormed env t of
        Nothing -> False
        Just env' -> loop env' u

newtype VarEnv = VarEnv (Map Id Term) deriving Show

emptyVarEnv :: VarEnv
emptyVarEnv = VarEnv M.empty

-- Check the structure and sort condition.

termWellFormed :: VarEnv -> Term -> Maybe VarEnv
termWellFormed xts t@(I x) =
  extendVarEnv xts x t          -- Mesg variable
termWellFormed xts t@(F Text [I x]) =
  extendVarEnv xts x t          -- Text variable
termWellFormed xts t@(F Data [I x]) =
  extendVarEnv xts x t          -- Data variable
termWellFormed xts t@(F Name [I x]) =
  extendVarEnv xts x t          -- Name variable
termWellFormed xts t@(F Skey [I x]) =
  extendVarEnv xts x t          -- Symmetric key variable
termWellFormed xts (F Skey [F Ltk [I x, I y]]) =
  -- Long term shared symmetric key
  doubleTermWellFormed xts (F Name [I x]) (F Name [I y])
termWellFormed xts (F Akey [t]) = -- Asymmetric key terms
  case t of
    I x -> extendVarEnv xts x (F Akey [I x])
    F Invk [I x] -> extendVarEnv xts x (F Akey [I x])
    F Pubk [I x] -> extendVarEnv xts x (F Name [I x])
    F Pubk [C _, I x] -> extendVarEnv xts x (F Name [I x])
    F Invk [F Pubk [I x]] -> extendVarEnv xts x (F Name [I x])
    F Invk [F Pubk [C _, I x]] -> extendVarEnv xts x (F Name [I x])
    _ -> Nothing
termWellFormed xts (F Base [t]) =
  baseVarEnv xts t
  where
    baseVarEnv xts t@(I x) =
      extendVarEnv xts x (F Base [t])
    baseVarEnv xts (F Genr []) =
      Just xts
    baseVarEnv xts (F Exp [t0, G t1]) =
      do
        xts <- baseVarEnv xts t0
        termWellFormed xts (G t1)
    baseVarEnv _ _ = Nothing
termWellFormed xts (G t) =
  foldM expnVarEnv xts (M.assocs t)
  where
    expnVarEnv xts (x, (be, _)) =
      extendVarEnv xts x (groupVar be x)
termWellFormed xts (C _) =
  Just xts                      -- Tags
termWellFormed xts (F Cat [t0, t1]) =
  doubleTermWellFormed xts t0 t1 -- Concatenation
termWellFormed xts (F Enc [t0, t1]) =
  doubleTermWellFormed xts t0 t1 -- Encryption
termWellFormed _ _ = Nothing

-- Extend when sorts agree
extendVarEnv :: VarEnv -> Id -> Term -> Maybe VarEnv
extendVarEnv (VarEnv env) x t =
  case M.lookup x env of
    Nothing -> Just $ VarEnv $ M.insert x t env
    Just t' -> if t == t' then Just (VarEnv env) else Nothing

doubleTermWellFormed :: VarEnv -> Term -> Term -> Maybe VarEnv
doubleTermWellFormed xts t0 t1 =
  do
    xts <- termWellFormed xts t0
    termWellFormed xts t1

-- Is the sort of the term a base sort?
isAtom :: Term -> Bool
isAtom (I _) = False
isAtom (C _) = False
isAtom (F Base [F Exp [F Genr [], G x]]) = isBasisVar x
isAtom (F s _) =
  s == Text || s == Data || s == Name || s == Skey || s == Akey
isAtom (G x) = isBasisVar x

-- Does a term occur in another term?

-- This function is always called with a variable that answers true to
-- isAcquiredVar as its first argument, so the first case never gets used.
occursIn :: Term -> Term -> Bool
occursIn (G t) (G t') =
  t == t'
occursIn t t' =
  t == t' ||
  case t' of
    F _ u -> any (occursIn t) u
    _ -> False

-- Fold f through a term applying it to each variable in the term.
foldVars :: (a -> Term -> a) -> a -> Term -> a
foldVars f acc t@(I _) = f acc t          -- Mesg variable
foldVars f acc t@(F Text [I _]) = f acc t -- Text variable
foldVars f acc t@(F Data [I _]) = f acc t -- Data variable
foldVars f acc t@(F Name [I _]) = f acc t -- Name variable
foldVars f acc t@(F Skey [I _]) =
  f acc t                       -- Symmetric key variable
foldVars f acc (F Skey [F Ltk [I x, I y]]) =
  -- Long term shared symmetric key
  f (f acc (F Name [I x])) (F Name [I y])
foldVars f acc t@(F Akey [I _]) = f acc t -- Asymmetric keys
foldVars f acc (F Akey [F Invk [I x]]) = f acc (F Akey [I x])
foldVars f acc (F Akey [F Pubk [I x]]) = f acc (F Name [I x])
foldVars f acc (F Akey [F Pubk [C _, I x]]) = f acc (F Name [I x])
foldVars f acc (F Akey [F Invk [F Pubk [I x]]]) = f acc (F Name [I x])
foldVars f acc (F Akey [F Invk [F Pubk [C _, I x]]]) = f acc (F Name [I x])
foldVars f acc (F Base [t]) =
  baseAddVars acc t
  where
    baseAddVars acc t@(I _) =
      f acc (F Base [t])
    baseAddVars acc (F Genr []) =
      acc
    baseAddVars acc (F Exp [t0, G t1]) =
      foldVars f (baseAddVars acc t0) (G t1)
    baseAddVars _ _ = error "Algebra.foldVars: Bad term"
foldVars f acc (G t) =
  foldl expnAddVars acc (M.assocs t)
  where
    expnAddVars acc (x, (be, _)) =
      f acc (groupVar be x)
foldVars _ acc (C _) = acc        -- Tags
foldVars f acc (F Cat [t0, t1]) = -- Concatenation
  foldVars f (foldVars f acc t0) t1
foldVars f acc (F Enc [t0, t1]) = -- Encryption
  foldVars f (foldVars f acc t0) t1
foldVars _ _ t = error $ "Algebra.foldVars: Bad term " ++ show t

-- Fold f through a term applying it to each term that is carried by the term.
foldCarriedTerms :: (a -> Term -> a) -> a -> Term -> a
foldCarriedTerms f acc t@(F Cat [t0, t1]) = -- Concatenation
  foldCarriedTerms f (foldCarriedTerms f (f acc t) t0) t1
foldCarriedTerms f acc t@(F Enc [t0, _]) = -- Encryption
  foldCarriedTerms f (f acc t) t0
foldCarriedTerms f acc t@(F Base [F Exp [_, t1]]) = -- Exponents
  f (f acc t) t1
foldCarriedTerms f acc t = f acc t     -- atoms and tags

-- Is a term carried by another term?
carriedBy :: Term -> Term -> Bool
carriedBy t t' =
  t == t' ||
  case t' of
    F Cat [t0, t1] -> carriedBy t t0 || carriedBy t t1
    F Enc [t0, _] -> carriedBy t t0
    _ -> False

-- The key used to decrypt an encrypted term, otherwise Nothing.
decryptionKey :: Term -> Maybe Term
decryptionKey (F Enc [_, t]) = Just (inv t)
decryptionKey _ = Nothing

buildable :: Set Term -> Set Term -> Term -> Bool
buildable knowns unguessable term =
  ba term
  where
    ba (I _) = True      -- A mesg sorted variable is always buildable
    ba (C _) = True      -- So is a tag
    ba (F Cat [t0, t1]) =
      ba t0 && ba t1
    ba t@(F Enc [t0, t1]) =
      S.member t knowns || ba t0 && ba t1
    ba (F Base [t]) = bb t
    ba t = isAtom t && S.notMember t unguessable
    -- Buildable base term
    bb (I _) = True     -- A variable of sort base is always buildable
    bb (F Genr []) = True       -- and so is the generator
    bb t@(F Exp [t0, G t1]) =
      S.member (F Base [t]) knowns || ba t0 && be t1
    bb (_) = False
    -- Buildable exponent
    be t =
      all (\x -> S.notMember x unguessable) (groupVars t)
    groupVars t = map (\(x, (be, _)) -> groupVar be x) (M.toList t)

-- Compute the decomposition given some known terms and some unguessable
-- atoms.  The code is quite tricky.  It iterates until the known
-- terms don't change.  The known terms ends up with all the
-- encryptions that are known.
decompose :: Set Term -> Set Term -> (Set Term, Set Term)
decompose knowns unguessable =
  loop unguessable knowns S.empty []
  where
    loop unguessable knowns old []
      | old == knowns = (knowns, unguessable) -- Done
      | otherwise = loop unguessable knowns knowns (S.elems knowns)
    loop unguessable knowns old (t@(F Cat _) : todo) =
      loop unguessable (decat t (S.delete t knowns)) old todo
    loop unguessable knowns old ((F Enc [t0, t1]) : todo)
      | buildable knowns unguessable (inv t1) = -- Add plaintext
        loop unguessable (decat t0 knowns) old todo
      | otherwise = loop unguessable knowns old todo
    loop unguessable knowns old (t : todo)
      | isAtom t =
        loop (S.delete t unguessable) (S.delete t knowns) old todo
      | otherwise = loop unguessable knowns old todo
    -- Decat
    decat (F Cat [t0, t1]) s = decat t1 (decat t0 s)
    decat t s = S.insert t s

-- Inverts an asymmetric key
inv :: Term -> Term
inv (F Akey [F Invk [t]]) = F Akey [t]
inv (F Akey [t]) = F Akey [F Invk [t]]
inv (I _) = error "Algebra.inv: Cannot invert a variable of sort mesg"
inv t = t

-- Extracts every encryption that is carried by a term along with its
-- encryption key.
encryptions :: Term -> [(Term, [Term])]
encryptions t =
  reverse $ loop t []
  where
    loop (F Cat [t, t']) acc =
      loop t' (loop t acc)
    loop t@(F Enc [t', t'']) acc =
      loop t' (adjoin (t, [t'']) acc)
    loop t@(F Base [F Exp [_, t'']]) acc =
      adjoin (t, [t'']) acc
    loop _ acc = acc
    adjoin x xs
      | x `elem` xs = xs
      | otherwise = x : xs

-- Returns the encryptions that carry the target.  If the target is
-- carried outside all encryptions, or is exposed because a decription
-- key is derivable, Nothing is returned.
protectors :: (Term -> Bool) -> Term -> Term -> Maybe [Term]
protectors derivable target source =
  do
    ts <- bare source S.empty
    return $ S.elems ts
  where
    bare source _
      | source == target = Nothing
    bare (F Cat [t, t']) acc =
      maybe Nothing (bare t') (bare t acc)
    bare t@(F Enc [t', key]) acc =
      if target `carriedBy` t' then
        if derivable (inv key) then
          bare t' acc
        else
          Just (S.insert t acc)
      else
        Just acc
    bare t@(F Base [F Exp [_, t'']]) acc
      | target == t'' = Just (S.insert t acc)
    bare _ acc = Just acc

-- Support for data flow analysis of traces.  A flow rule maps an
-- initial set of atoms and a set of available terms to sets of pairs
-- of the same sets.
type FlowRule = (Set Term, Set Term) -> Set (Set Term, Set Term)

-- Combine flow rules sequentially.
comb :: FlowRule -> FlowRule -> FlowRule
comb f g x =
  S.fold h S.empty (g x)
  where
    h a s = S.union (f a) s

-- Analyze a term as a sent term.
outFlow :: Term -> FlowRule
outFlow t a@(_, available)
  | S.member t available = S.singleton a
outFlow (I _) _ = S.empty
outFlow (C _) a = S.singleton a
outFlow (F Cat [t0, t1]) a =    -- Construct non-atoms
  comb (outFlow t1) (outFlow t0) a
outFlow (F Enc [t0, t1]) a =
  comb (outFlow t1) (outFlow t0) a
outFlow t (initial, available) = -- Don't look inside atoms
  S.singleton (S.insert t initial, S.insert t available)

-- Analyze a term as a received term.
inFlow :: Term -> FlowRule
inFlow (C _) a = S.singleton a
inFlow (F Cat [t0, t1]) a =     -- Try to receive components
  S.union                       -- in both orders
  (comb (inFlow t1) (inFlow t0) a)
  (comb (inFlow t0) (inFlow t1) a)
inFlow t@(F Enc [t0, t1]) (initial, available) =
  S.union                     -- Encryption can be built
  (outFlow t (initial, available)) -- or decrypted
  (comb (inFlow t0) (outFlow (inv t1)) a)
  where                       -- Derive decryption key first
    a = (initial, S.insert t available)
inFlow t (initial, available) =
  S.singleton (initial, S.insert t available)

instance C.Term Term where
  isVar = isVar
  isAcquiredVar = isAcquiredVar
  isAtom = isAtom
  termsWellFormed = termsWellFormed
  occursIn = occursIn
  foldVars = foldVars
  foldCarriedTerms = foldCarriedTerms
  carriedBy = carriedBy
  decryptionKey = decryptionKey
  decompose = decompose
  buildable = buildable
  encryptions = encryptions
  protectors = protectors
  outFlow = outFlow
  inFlow = inFlow
  loadTerm = loadTerm

-- Places

-- A place names a one subterm within a term.  It is a list of
-- integers giving a path through a term to that named subterm.  Each
-- integer in the list identifies the subterm in a function
-- application on the path to the named subterm.  The integer is the
-- index of the subterm in the application's list of terms.

-- The places and replace code fail to find the variable
-- (F Akey [I x]) in (F Akey [Invk [I x]]).

newtype Place = Place [Int] deriving Show

-- Returns the places a variable occurs within a term.
-- Returns no places for group variables.
places :: Term -> Term -> [Place]
places var source =
  f [] [] source
  where
    f paths path source
      | var == source = Place (reverse path) : paths
    f paths path (F _ u) =
      g paths path 0 u
    f paths _ _ = paths
    g paths _ _ [] = paths
    g paths path i (t : u) =
      g (f paths (i: path) t) path (i + 1) u

-- Returns the places a term is carried by another term.
carriedPlaces :: Term -> Term -> [Place]
carriedPlaces target source =
  f [] [] source
  where
    f paths path source
      | target == source = Place (reverse path) : paths
    f paths path (F Cat [t, t']) =
      f (f paths  (0 : path) t) (1 : path) t'
    f paths path (F Enc [t, _]) =
      f paths (0 : path) t
    f paths _ _ = paths

-- Replace a variable within a term at a given place.
replace :: Term -> Place -> Term -> Term
replace var (Place ints) source =
  loop ints source
  where
    loop [] _ = var
    loop (i : path) (F s u) =
      F s (C.replaceNth (loop path (u !! i)) i u)
    loop _ (G _) = error "Algebra.replace: Path to expn"
    loop _ _ = error "Algebra.replace: Bad path to term"

-- Return the ancestors of the term at the given place.
ancestors :: Term -> Place -> [Term]
ancestors source (Place ints) =
  loop [] ints source
  where
    loop ts [] _ = ts
    loop ts (i: path) t@(F _ u) =
      loop (t : ts) path (u !! i)
    loop _ _ _ = error "Algebra.ancestors: Bad path to term"

instance C.Place Term Place where
  places = places
  carriedPlaces = carriedPlaces
  replace = replace
  ancestors = ancestors

-- Rename the identifiers in a term.  Gen keeps the state of the
-- renamer.  (Question: should alist be replaced by a Map?)
clone :: Gen -> Term -> (Gen, Term)
clone gen t =
  (gen', t')
  where
    (_, gen', t') = cloneTerm ([], gen) t
    cloneTerm (alist, gen) t =
      case t of                 -- The association list maps
        I x ->                  -- identifiers to identifier.
          case lookup x alist of
            Just y -> (alist, gen, I y)
            Nothing ->
              let (gen', y) = cloneId gen x in
              ((x, y) : alist, gen', I y)
        C c -> (alist, gen, C c)
        F sym u ->
          let (alist', gen', u') =
                foldl cloneTermList (alist, gen, []) u in
          (alist', gen', F sym $ reverse u')
        G t ->
          let (alist', gen', ts) =
                foldl cloneGroupList (alist, gen, []) (M.assocs t) in
          (alist', gen', G $ group ts)
    cloneTermList (alist, gen, u) t =
      let (alist', gen', t') = cloneTerm (alist, gen) t in
      (alist', gen', t' : u)
    cloneGroupList (alist, gen, ts) (x, (be, c)) =
      case lookup x alist of
        Just y -> (alist, gen, (y, (be, c)) : ts)
        Nothing ->
          let (gen', y) = cloneId gen x in
          ((x, y) : alist, gen', (y, (be, c)) : ts)

instance C.Gen Term Gen where
  origin = origin
  clone = clone
  loadVars = loadVars

-- Functions used in both unification and matching

type IdMap = Map Id Term

emptyIdMap :: IdMap
emptyIdMap = M.empty

-- Apply a substitution to a term
idSubst :: IdMap -> Term -> Term
idSubst subst (I x) =
  M.findWithDefault (I x) x subst
idSubst _ t@(C _) = t
idSubst subst (F Invk [t]) =
  case idSubst subst t of
    F Invk [t] -> t             -- (invk (invk x)) = x
    t -> F Invk [t]
idSubst subst (F Exp [t0, G t1]) =
  case idSubst subst t0 of    -- (exp (exp g x) y) = (exp g (mul x y))
    F Exp [t0', G t1'] ->
      case mul t1' $ groupSubst subst t1 of
        t2 | M.null t2 -> t0'
           | otherwise -> F Exp [t0', G t2]
    t -> expSubst subst t t1
idSubst subst (F s u) =
  F s (map (idSubst subst) u)
idSubst subst (G t) =
  G $ groupSubst subst t

expSubst :: IdMap -> Term -> Group -> Term
expSubst subst t0 t1 =
  case groupSubst subst t1 of
    t1' | M.null t1' -> t0    -- (exp g (one)) = g
        | otherwise -> F Exp [t0, G t1']

groupSubst :: IdMap -> Group -> Group
groupSubst subst t =
  M.foldrWithKey f M.empty t
  where
    f x (be, c) t =
      mul (expg (groupLookup subst be x) c) t

groupLookup :: IdMap -> Bool -> Id -> Group
groupLookup subst be x =
  case M.findWithDefault (groupVar be x) x subst of
    G t -> t
    w -> error ("Algebra.groupLookup: Bad substitution: " ++
                show x ++ " -> " ++ show w)

showMap :: (Show a, Show b) => Map a b -> ShowS
showMap m =
  showAssocs (M.assocs m)
  where
    showAssocs [] = id
    showAssocs ((x,y):m) =
      showString "\n " . shows x . showString " -> " .
      shows y . showAssocs m

-- Unification and substitution

-- The rewrite rules used are:
--
-- (vars (h base) (x y expn))
--
-- 1.  ((exp h x) y) ==> (exp h (mul x y))
-- 2.  (exp h (one)) ==> h
-- 3.  unify((exp h x), (exp h y), s) ==>
--         unify(x, y, s)
-- 4   unify((exp h x), (exp (gen) y), s) ==>
--         unify(h, (exp gen (mul y (rec x))), s)
-- 5.  unify((exp (gen) x), (exp h y), s) ==>
--         unify((exp h x), (exp (gen) y), s)

newtype Subst = Subst IdMap deriving (Eq, Ord)

instance Show Subst where
  showsPrec _ (Subst s) = showString "Subst (" . showMap s . showChar ')'

emptySubst :: Subst
emptySubst = Subst emptyIdMap

-- Apply a substitution created by unification
substitute :: Subst -> Term -> Term
substitute (Subst s) t =
  idSubst s t

-- Composition of substitutions

-- substitute (compose s0 s1) t = substitute s0 (substitute s1 t)

-- 1. apply s0 to range of s1 to obtain s2;
-- 2. remove bindings is s0 where domains of s0 and s1 overlap to form s3;
-- 3. remove trivial bindings from s2 to form s4; and
-- 4. take the union of s4 and s3.

compose :: Subst -> Subst -> Subst
compose (Subst s0) (Subst s1) =
  let s2 = M.map (substitute (Subst s0)) s1        -- Step 1
      s4 = M.filterWithKey nonTrivialBinding s2 in -- Step 3
  Subst (M.union s4 s0)       -- Steps 2 and 4, union is left-biased

nonTrivialBinding :: Id -> Term -> Bool
nonTrivialBinding x (I y) = x /= y
nonTrivialBinding x (G y) | isGroupVar y = x /= getGroupVar y
nonTrivialBinding _ _ = True

-- During unification, variables determined to be equal are collected
-- into an equivalence class.  Multiple lookups of each variable in
-- the internal representation of a substitution finds the canonical
-- representive of the class.  The chase function finds the current
-- canonical representitive.

-- Get the canonical representative of equivalent identifiers making use
-- of this algebra's axiom.
chase :: Subst -> Term -> Term
chase (Subst s) (I x) =
  case M.lookup x s of
    Nothing -> I x
    Just t -> chase (Subst s) t
chase s (F Invk [t]) = chaseInvk s t
chase s (F Exp [t0, G t1]) = chaseExp s t0 t1
chase _ t = t

chaseInvk :: Subst -> Term -> Term
chaseInvk (Subst s) (I x) =
  case M.lookup x s of
    Nothing -> F Invk [I x]
    Just t -> chaseInvk (Subst s) t
chaseInvk s (F Invk [t]) = chase s t
chaseInvk _ t = F Invk [t]

chaseExp :: Subst -> Term -> Group -> Term
chaseExp s t0 t1
  | M.null t1 = chase s t0
chaseExp s (I x) t1 =
  case chase s (I x) of
    F Exp [t0', G t1'] -> chaseExp s t0' (mul t1 t1')
    t0 -> F Exp [t0, chaseGroup s t1]
chaseExp s (F Exp [t0', G t1']) t1 =
  chaseExp s t0' (mul t1 t1')
chaseExp s t0 t1 = F Exp [t0, chaseGroup s t1]

chaseGroup :: Subst -> Group -> Term
chaseGroup (Subst s) x = G $ groupSubst s x

-- Does x occur in t?
occurs :: Id -> Term -> Bool
occurs x (I y) = x == y
occurs _ (C _) = False
occurs x (F _ u) = any (occurs x) u
occurs x (G t) = elem x (M.keys t)

type GenSubst = (Gen, Subst)

unifyChase :: Term -> Term -> GenSubst -> [GenSubst]
unifyChase t t' (g, s) = unifyTerms (chase s t) (chase s t') (g, s)

unifyTerms :: Term -> Term -> GenSubst -> [GenSubst]
unifyTerms (I x) (I y) (g, Subst s)
  | x == y = [(g, Subst s)]
  | otherwise = [(g, Subst $ M.insert x (I y) s)]
unifyTerms (I x) t (g, Subst s)
  | occurs x t = []
  | otherwise = [(g, Subst $ M.insert x t s)]
unifyTerms t (I x) s = unifyTerms (I x) t s
unifyTerms (C c) (C c') s
  | c == c' = [s]
  | otherwise = []
unifyTerms (F Invk [I x]) (F Pubk [I y]) s =
  unifyTerms (I x) (F Invk [F Pubk [I y]]) s
unifyTerms (F Invk [I x]) (F Pubk [C c, I y]) s =
  unifyTerms (I x) (F Invk [F Pubk [C c, I y]]) s
unifyTerms (F Pubk [I x]) (F Invk [I y]) s =
  unifyTerms (I y) (F Invk [F Pubk [I x]]) s
unifyTerms (F Pubk [C c, I x]) (F Invk [I y]) s =
  unifyTerms (I y) (F Invk [F Pubk [C c, I x]]) s
unifyTerms (F Exp [t0, G t1]) (F Exp [t0', G t1']) s =
  unifyExp t0 t1 t0' t1' s
unifyTerms (F sym u) (F sym' u') s
  | sym == sym' = unifyTermLists u u' s
  | otherwise = []
unifyTerms (G t) (G t') s = unifyGroup t t' s
unifyTerms _ _ _ = []

unifyExp :: Term -> Group -> Term -> Group -> GenSubst -> [GenSubst]
unifyExp t0 t1 t0' t1' s
  | t0 == t0' = unifyGroup t1 t1' s
unifyExp (I x) t1 (F Genr []) t1' (g, Subst s)
  | t1 == t1' =
    [(g, Subst $ M.insert x (F Genr []) s)]
  | otherwise =
    [(g, Subst (M.insert
                x
                (F Exp [F Genr [], G $ mul t1' (invert t1)])
                s))]
unifyExp (F Genr []) t1 (I x) t1' s =
  unifyExp (I x) t1' (F Genr []) t1 s
unifyExp _ _ _ _ _ = []

unifyTermLists :: [Term] -> [Term] -> GenSubst -> [GenSubst]
unifyTermLists [] [] s = [s]
unifyTermLists (t : u) (t' : u') s =
  do
    s' <- unifyChase t t' s
    unifyTermLists u u' s'
unifyTermLists _ _ _ = []

unifyGroup :: Group -> Group -> GenSubst -> [GenSubst]
unifyGroup t0 t1 (g, Subst s) =
  do
    (_, g', s') <- matchGroup (groupSubst s $ mul t0 $ invert t1)
                   M.empty S.empty g
    return (g', Subst $ M.union s' s)

-- The exported unifier converts the internal representation of a
-- substitution into the external form using chaseMap.

unify :: Term -> Term -> GenSubst -> [GenSubst]
unify t t' s =
  do
    (g, s) <- unifyChase t t' s
    return (g, chaseMap s)

-- Apply the chasing version of substitution to the range of s.

chaseMap :: Subst -> Subst
chaseMap (Subst s) =
  Subst $ M.map (substChase (Subst s)) s

-- A chasing version of substitution.

substChase :: Subst -> Term -> Term
substChase subst t =
  case chase subst t of
    t@(I _) -> t
    t@(C _) -> t
    F Invk [t] ->
        case substChase subst t of
          F Invk [t] -> t           -- Apply axiom
          t -> F Invk [t]
    F Exp [t0, G t1] ->
        case substChase subst t0 of
          F Exp [t0', G t1'] ->
            case mul t1' $ groupChase subst t1 of
              t2 | M.null t2 -> t0'
                 | otherwise -> F Exp [t0', G t2]
          t -> expChase subst t t1
    F s u ->
        F s (map (substChase subst) u)
    G t -> G $ groupChase subst t

expChase :: Subst -> Term -> Group -> Term
expChase subst t0 t1 =
  case groupChase subst t1 of
    t1' | M.null t1' -> t0
        | otherwise -> F Exp [t0, G t1']

groupChase :: Subst -> Group -> Group
groupChase (Subst subst) t = groupSubst subst t

instance C.Subst Term Gen Subst where
 emptySubst = emptySubst
 substitute = substitute
 unify = unify
 compose = compose

-- Matching and instantiation

newtype Env = Env (Set Id, IdMap) deriving (Eq, Ord)

instance Show Env where
  showsPrec _ (Env (v, r)) =
      showString "Env (\n " . shows v .
      showChar ',' . showMap r . showChar ')'

-- An environment may contain an explicit identity mapping, whereas a
-- substitution is erroneous if it has one.  The set of variables
-- associated with a map is the variables in the range that were
-- generated by matching and should be treated as variables when using
-- unification to perform matching.  The other variables in the range
-- are treated as constants.

-- An environment contains an IdMap and the set of variables
-- generated while matching.

emptyEnv :: Env
emptyEnv = Env (S.empty, emptyIdMap)

-- Apply a substitution created my matching
instantiate :: Env -> Term -> Term
instantiate (Env (_, r)) t = idSubst r t

-- Matching

type GenEnv = (Gen, Env)

-- The matcher has the property that when pattern P and term T match
-- then instantiate (match P T emptyEnv) P = T.
match ::  Term -> Term -> GenEnv -> [GenEnv]
match (I x) t (g, Env (v, r)) =
  case M.lookup x r of
    Nothing -> [(g, Env (v, M.insert x t r))]
    Just t' -> if t == t' then [(g, Env (v, r))] else []
match (C c) (C c') r = if c == c' then [r] else []
match (F Exp [t0, G t1]) (F Exp [t0', G t1']) r
    = matchExp t0 t1 t0' t1' r
match (F s u) (F s' u') r
  | s == s' = matchLists u u' r
match (F Invk [t]) t' r =
  match t (F Invk [t']) r
match (G t) (G t') (g, Env (v, r)) =
  do
    let (t0, t0') = merge t t' r
    (v, g, r') <- matchGroup t0 t0' v g
    return (g, Env (v, M.union r' r))
match _ _ _ = []

matchExp ::  Term -> Group -> Term -> Group -> GenEnv -> [GenEnv]
matchExp (I x) t1 t0' t1' r@(_, Env (_, e)) =
  case M.lookup x e of
    Just (F Exp [t0'', G t1''])
        | t0' == t0'' -> match (G t1) (G (mul t1' (invert t1''))) r
    _ -> matchLists [I x, G t1] [t0', G t1'] r
matchExp (F Genr []) t1 t0' t1' r =
  matchLists [F Genr [], G t1] [t0', G t1'] r
matchExp _ _ _ _ _ = error "Algebra.matchExp: Bad match term"

matchLists :: [Term] -> [Term] -> GenEnv -> [GenEnv]
matchLists [] [] r = [r]
matchLists (t : u) (t' : u') r =
  do
    r' <- match t t' r
    matchLists u u' r'
matchLists _ _ _ = []

-- Merge the previous bindings in r into the current matching problem.
-- For each maplet in t, if r contains a mapping, apply the mapping
-- and move the result to the RHS.
merge ::  Group -> Group -> IdMap -> (Group, Group)
merge t t' r =
  (group t0, t0')
  where
    (t0, t0') = loop (M.assocs t) ([], t')
    loop [] acc = acc
    loop (p@(x, (_, c)) : t0) (t1, t1') =
      case M.lookup x r of
        Nothing -> loop t0 (p : t1, t1')
        Just (G t) ->
          loop t0 (t1, mul (expg t (negate c)) t1')
        Just t ->
          error $ "Algebra.merge: expecting an expn but got " ++ show t

-- Matching in a group

-- t0 is the pattern
-- t1 is the target term
-- v is the set of previously freshly generated variables
-- g is the generator

-- Returns complete set of unifiers.  Each unifier include the set of
-- variables fresh generated and a generator.

-- Freshly generated variables are of sort expn.
matchGroup ::  Group -> Group -> Set Id -> Gen -> [(Set Id, Gen, IdMap)]
matchGroup t0 t1 v g =
  case partition t0 t1 v of
    ([], []) -> return (v, g, emptyIdMap)
    ([], t) -> constSolve t v g
    (t0, t1) -> solve t0 t1 v g emptyIdMap mkDecis

-- Move variables on the RHS of the equation to the LHS
-- Move variables of sort elem on the LHS to the RHS
partition ::  Group -> Group -> Set Id -> ([Maplet], [Maplet])
partition t0 t1 v =
  (M.assocs lhs, M.assocs rhs)
  where
    (v1, c1) = M.partitionWithKey g t1 -- Fresh variables go in v1
    g x _ = S.member x v
    (v0, c0) = M.partition f t0        -- Basis elements go in c0
    f (be, _) = not be
    lhs = mul v0 (invert v1)
    rhs = mul c1 (invert c0)

constSolve :: [Maplet] -> Set Id -> Gen -> [(Set Id, Gen, IdMap)]
constSolve t v g
  | any (\(_, (be, _)) -> not be) t = []
  | otherwise = constSolve1 t v g emptyIdMap mkDecis
                
constSolve1 :: [Maplet] -> Set Id -> Gen ->
               IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
constSolve1 [] v g r _ = return (v, g, r)
constSolve1 t v g r d =
  case nextDecis d t of
    [] -> []
    ((x, y):_) ->
      distinct ++ identified
      where
        distinct = constSolve1 t v g r neq
        neq = d {dist = (x, y):(y, x):dist d}
        -- eliminate x
        identified = constSolve1 t' v g r' d'
        t' = identify x y t
        r' = M.insert x y' (eliminate x y' r)
        y' = groupVar True y
        d' = d {same = (x, y):same d}

solve ::  [Maplet] -> [Maplet] -> Set Id -> Gen ->
          IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
solve t0 t1 v g r d =
  let (x, ci, i) = smallest t0 in
  case compare ci 0 of
    GT -> solve1 x ci i t0 t1 v g r d
    LT -> solve1 x (-ci) i (mInverse t0) t1 v g r d
    EQ -> error "Algebra.solve: zero coefficient found"

smallest :: [Maplet] -> (Id, Int, Int)
smallest [] = error "Algebra.smallest given an empty list"
smallest t =
  loop (Id (0, "x")) 0 0 0 0 t
  where
    loop v ci i _ _ [] = (v, ci, i)
    loop v ci i a j ((x, (_, c)):t) =
      if a < abs c then
        loop x c j (abs c) (j + 1) t
      else
        loop v ci i a (j + 1) t

solve1 :: Id -> Int -> Int -> [Maplet] -> [Maplet] -> Set Id -> Gen ->
          IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
solve1 x 1 i t0 t1 v g r _ =    -- Solve for x and return answer
  return (v, g, M.insert x t (eliminate x t r))
  where
    t = G $ group (t1 ++ (mInverse (omit i t0)))
solve1 x ci i t0 t1 v g r d
  | divisible ci t0 =
    if divisible ci t1 then
      solve1 x 1 i (divide ci t0) (divide ci t1) v g r d
    else
      solve2 x ci i t0 t1 v g r d
  | otherwise =
      solve t0' t1 (S.insert x' v) g' r' d
      where
        (g', x') = cloneId g x
        t = G $ group ((x', (False, 1)) :
                       mInverse (divide ci (omit i t0)))
        r' = M.insert x t (eliminate x t r)
        t0' = (x', (False, ci)) : modulo ci t0

eliminate :: Id -> Term -> IdMap -> IdMap
eliminate x t r =
  M.map (idSubst (M.singleton x t)) r

omit :: Int -> [a] -> [a]
omit 0 (_:l) = l
omit n _ | n < 0 = error "Algebra.omit: negative number given to omit"
omit n (_:l) = omit (n - 1) l
omit _ [] = error "Algebra.omit: number given to omit too large"

divisible :: Int -> [Maplet] -> Bool
divisible ci t =
  all (\(_, (_, c)) -> mod c ci == 0) t

divide :: Int -> [Maplet] -> [Maplet]
divide ci t = map (mMapCoef $ flip div ci) t

modulo :: Int -> [Maplet] -> [Maplet]
modulo ci t =
  [(x, (be, c')) |
   (x, (be, c)) <- t,
   let c' = mod c ci,
   c' /= 0]

data Decision t = Decision
  { same :: [(t, t)],
    dist :: [(t, t)] }
  deriving Show

mkDecis :: Decision Id
mkDecis =
  Decision {
    same = [],
    dist = [] }

solve2 :: Id -> Int -> Int -> [Maplet] -> [Maplet] -> Set Id -> Gen ->
          IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
solve2 z ci i t0 t1 v g r d =
  case nextDecis d t1 of
    [] -> []
    ((x, y):_) ->
      distinct ++ identified
      where
        distinct = solve2 z ci i t0 t1 v g r neq
        neq = d {dist = (x, y):(y, x):dist d}
        -- eliminate x
        identified = solve1 z ci i t0 t1' v g r' d'
        t1' = identify x y t1
        r' = M.insert x y' (eliminate x y' r)
        y' = groupVar True y
        d' = d {same = (x, y):same d}

nextDecis :: Decision Id -> [Maplet] -> [(Id, Id)]
nextDecis d t =
  [(x, y) | x <- vars, y <- vars, x < y,
    not $ decided d x y]
  where
    vars = foldr f [] t
    f (x, (True, _)) v = x:v
    f (_, (False, _)) v = v
    decided d x y =
      u == v ||
      any f (dist d)
      where
        u = chase x
        v = chase y
        f (w, z) = chase w == u && chase z == v
        chase = listChase (same d)

listChase :: Eq t => [(t, t)] -> t -> t
listChase d x =
  case lookup x d of
    Nothing -> x
    Just y -> listChase d y

identify :: Id -> Id -> [Maplet] -> [Maplet]
identify x y t =
  case lookup x t of
    Nothing -> error ("Algebra.identify: bad lookup of " ++ show x
                      ++ " in " ++ show t)
    Just (_, c) ->
      filter f (map g t)
      where
        f (z, (_, c)) = z /= x && c /= 0
        g m@(z, (be, d))
          | z == y = (z, (be, c + d))
          | otherwise = m

-- Does every varible in ts not occur in the domain of e?
-- Trivial bindings in e are ignored.
identityEnvFor :: GenEnv -> [Term] -> [GenEnv]
identityEnvFor ge ts =
  let env@(_, Env (_, r)) = nonTrivialEnv ge in
  if all (allId $ flip S.notMember $ M.keysSet r) ts then
      [env]
  else
      []

allId :: (Id -> Bool) -> Term -> Bool
allId f (I x) = f x
allId _ (C _) = True
allId f (F _ u) = all (allId f) u
allId f (G t) = all f (M.keys t)

-- Eliminate all trivial bindings so that an environment can be used
-- as a substitution.
nonTrivialEnv :: GenEnv -> GenEnv
nonTrivialEnv (g, Env (v, r)) =
  (g, Env (v, M.filterWithKey nonTrivialBinding r))

{--
nonTrivialEnv (g, Env (v, r)) =
  nonGroupEnv (M.assocs r) M.empty []
  where
    nonGroupEnv [] env grp =
      groupEnv g v env grp grp
    nonGroupEnv ((x, I y):r) env grp
      | x == y = nonGroupEnv r env grp
    nonGroupEnv ((x, G y):r) env grp
      | isGroupVar y && getGroupVar y == x =
        nonGroupEnv r env grp
      | otherwise = nonGroupEnv r env ((x, y):grp)
    nonGroupEnv ((x, y):r) env grp =
      nonGroupEnv r (M.insert x y env) grp

groupEnv :: Gen -> Set Id -> IdMap -> [(Id, Group)] -> [(Id, Group)] -> GenEnv
groupEnv g v env grp [] =
  (g, Env (v, foldl (\env (x, y) -> M.insert x (G y) env) env grp))
groupEnv g v env grp ((x, t):map)
  | M.lookup x t /= Just 1 = groupEnv g v env grp map
  | otherwise =
      let (t0, t1) = partition M.empty (mul t (M.singleton x (-1))) v in
      case matchGroup (group t0) (group t1) S.empty g of
        Nothing -> groupEnv g v env grp map
        Just (v', g', subst) ->
            let grp' = L.delete (x, t) grp
                grp'' = L.map (\(x, t) -> (x, groupSubst subst t)) grp' in
            groupEnv g' (S.union v' v) env grp'' grp''

notGroupVarMap :: Id -> Group -> Bool
notGroupVarMap x grp =
  case M.lookup x t of
    Nothing -> True
    Just (_, (_, c)) -> c /= 1

-}

substitution :: Env -> Subst
substitution (Env (_, r)) =
  Subst $ M.filterWithKey nonTrivialBinding r

-- Add type information to an environment, and return it as a list of
-- associations.

reify :: [Term] -> Env -> [(Term, Term)]
reify domain (Env (_, env)) =
  map (loop domain) $ M.assocs env
  where
    loop [] (x, _) =
      error $ "Algebra.reify: variable missing from domain " ++ idName x ++ "\n" ++ show domain ++ "\n" ++ show env
    loop (I x : _) (y, t)
      | x == y = (I x, t)
    loop (F Text [I x] : _) (y, t)
      | x == y = (F Text [I x], F Text [t])
    loop (F Data [I x] : _) (y, t)
      | x == y = (F Data [I x], F Data [t])
    loop (F Name [I x] : _) (y, t)
      | x == y = (F Name [I x], F Name [t])
    loop (F Skey [I x] : _) (y, t)
      | x == y = (F Skey [I x], F Skey [t])
    loop (F Akey [I x] : _) (y, t)
      | x == y = (F Akey [I x], F Akey [t])
    loop (F Base [I x] : _) (y, t)
      | x == y = (F Base [I x], F Base [t])
    loop (G x : _) (y, G t)
      | isGroupVar x && getGroupVar x == y = (G x, G t)
    loop (_ : domain) pair = loop domain pair

-- Ensure the range of an environment contains only variables and that
-- the environment is injective.
matchRenaming :: GenEnv -> Bool
matchRenaming (_, Env (_, e)) =
  loop S.empty $ M.elems e
  where
    loop _ [] = True
    loop s (I x:e) =
      S.notMember x s && loop (S.insert x s) e
    loop s (G y:e) | isGroupVar y =
      let x = getGroupVar y in
      S.notMember x s && loop (S.insert x s) e
    loop _ _ = False

{--
-- Ensure the range of an environment contains only variables and that
-- the environment is injective.
matchRenaming :: GenEnv -> Bool
matchRenaming (gen, Env (v, e)) =
  nonGrp S.empty (M.elems e) &&
  groupMatchRenaming v gen (M.foldrWithKey grp M.empty e)
  where
    nonGrp _ [] = True
    nonGrp s (I x:e) =
      S.notMember x s && nonGrp (S.insert x s) e
    nonGrp s (G _:e) = nonGrp s e -- Check group bindings elsewhere
    nonGrp _ _ = False
    grp x (G t) map = M.insert x t map
    grp _ _ map = map           -- Get rid of non-group bindings

groupMatchRenaming :: Set Id -> Gen -> Map Id Group -> Bool
groupMatchRenaming v gen map =
  loop S.empty $ M.elems map
  where
    loop _ [] = True
    loop s (t:ge)
      | M.null t = False
      | isGroupVar t =
        let x = getGroupVar t in
        S.notMember x s && loop (S.insert x s) ge
      | otherwise = any (groupMatchElim v gen map t) (M.assocs t)

groupMatchElim :: Set Id -> Gen -> Map Id Group -> Group -> Maplet -> Bool
groupMatchElim v gen ge t (x, (be, 1)) =
  let (t0, t1) = partition M.empty (mul t (mlGrp (x, (be, -1)))) v in
  any f (matchGroup (group t0) (group t1) S.empty gen)
  where
    f (v', gen', subst) =
      groupMatchRenaming (S.union v' v) gen' $ M.map (groupSubst subst) ge
groupMatchElim _ _ _ _ _ = False
-}

instance C.Env Term Gen Subst Env where
  emptyEnv = emptyEnv
  instantiate = instantiate
  match = match
  identityEnvFor = identityEnvFor
  substitution = substitution
  reify = reify
  matchRenaming = matchRenaming

-- Term specific loading functions

loadVars :: Monad m => Gen -> [SExpr Pos] -> m (Gen, [Term])
loadVars gen sexprs =
  do
    pairs <- mapM loadVarPair sexprs
    (g, vars) <- foldM loadVar (gen, []) (concat pairs)
    return (g, reverse vars)

loadVarPair :: Monad m => SExpr Pos -> m [(SExpr Pos, SExpr Pos)]
loadVarPair (L _ (x:xs)) =
  let (t:vs) = reverse (x:xs) in
  return [(v,t) | v <- reverse vs]
loadVarPair x = fail (shows (annotation x) "Bad variable declaration")

loadVar :: Monad m => (Gen, [Term]) -> (SExpr Pos, SExpr Pos) ->
           m (Gen, [Term])
loadVar (gen, vars) (S pos name, S pos' sort) =
  case loadLookup pos vars name of
    Right _ ->
      fail (shows pos "Duplicate variable declaration for " ++ name)
    Left _ ->
      do
        let (gen', x) = freshId gen name
        p <- mkVar x
        return (gen', p : vars)
  where
    mkVar x =
      let t = I x in
      case sort of
        "mesg" -> return t
        "text" -> return $ F Text [t]
        "data" -> return $ F Data [t]
        "name" -> return $ F Name [t]
        "skey" -> return $ F Skey [t]
        "akey" -> return $ F Akey [t]
        "base" -> return $ F Base [t]
        "expn" -> return $ groupVar False x
        "elem" -> return $ groupVar True x
        _ -> fail (shows pos' "Sort " ++ sort ++ " not recognized")
loadVar _ (x,_) = fail (shows (annotation x) "Bad variable syntax")

loadLookup :: Pos -> [Term] -> String -> Either String Term
loadLookup pos [] name = Left (shows pos $ "Identifier " ++ name ++ " unknown")
loadLookup pos (t : u) name =
  let name' = idName (varId t) in
  if name' == name then Right t else loadLookup pos u name

loadLookupName :: Monad m => Pos -> [Term] -> String -> m Term
loadLookupName pos vars name =
  either fail f (loadLookup pos vars name)
  where
    f t@(F Name [I _]) = return t
    f _ = fail (shows pos $ "Expecting " ++ name ++ " to be a name")

loadLookupAkey :: Monad m => Pos -> [Term] -> String -> m Term
loadLookupAkey pos vars name =
  either fail f (loadLookup pos vars name)
  where
    f t@(F Akey [I _]) = return t
    f _ = fail (shows pos $ "Expecting " ++ name ++ " to be an akey")

-- Load term and check that it is well-formed.
loadTerm :: Monad m => [Term] -> SExpr Pos -> m Term
loadTerm vars (S pos s) =
  either fail return (loadLookup pos vars s)
loadTerm _ (Q _ t) =
  return (C t)
loadTerm vars (L pos (S _ s : l)) =
  case lookup s loadDispatch of
    Nothing -> fail (shows pos "Keyword " ++ s ++ " unknown")
    Just f -> f pos vars l
loadTerm _ x = fail (shows (annotation x) "Malformed term")

type LoadFunction m = Pos -> [Term] -> [SExpr Pos] -> m Term

loadDispatch :: Monad m => [(String, LoadFunction m)]
loadDispatch =
  [("pubk", loadPubk)
  ,("privk", loadPrivk)
  ,("invk", loadInvk)
  ,("ltk", loadLtk)
  ,("gen", loadGen)
  ,("exp", loadExp)
  ,("one", loadOne)
  ,("rec", loadRec)
  ,("mul", loadMul)
  ,("cat", loadCat)
  ,("enc", loadEnc)
  ]

-- Atom constructors: pubk privk invk ltk

loadPubk :: Monad m => LoadFunction m
loadPubk _ vars [S pos s] =
  do
    t <- loadLookupName pos vars s
    return $ F Akey [F Pubk [I $ varId t]]
loadPubk _ vars [Q _ c, S pos s] =
  do
    t <- loadLookupName pos vars s
    return $ F Akey [F Pubk [C c, I $ varId t]]
loadPubk pos _ _ = fail (shows pos "Malformed pubk")

loadPrivk :: Monad m => LoadFunction m
loadPrivk _ vars [S pos s] =
  do
    t <- loadLookupName pos vars s
    return $ F Akey [F Invk [F Pubk [I $ varId t]]]
loadPrivk _ vars [Q _ c, S pos s] =
  do
    t <- loadLookupName pos vars s
    return $ F Akey [F Invk [F Pubk [C c, I $ varId t]]]
loadPrivk pos _ _ = fail (shows pos "Malformed privk")

loadInvk :: Monad m => LoadFunction m
loadInvk _ vars [S pos s] =
  do
    t <- loadLookupAkey pos vars s
    return $ F Akey [F Invk [I $ varId t]]
loadInvk pos _ _ = fail (shows pos "Malformed invk")

loadLtk :: Monad m => LoadFunction m
loadLtk _ vars [S pos s, S pos' s'] =
  do
    t <- loadLookupName pos vars s
    t' <- loadLookupName pos' vars s'
    return $ F Skey [F Ltk [I $ varId t, I $ varId t']]
loadLtk pos _ _ = fail (shows pos "Malformed ltk")

-- Base and exponents

loadGen :: Monad m => LoadFunction m
loadGen _ _ [] =
  return $ F Base [F Genr []]
loadGen pos _ _ = fail (shows pos "Malformed gen")

loadExp :: Monad m => LoadFunction m
loadExp _ vars [x, x'] =
  do
    t <- loadBase vars x
    t' <- loadExpn vars x'
    return $ F Base [idSubst emptyIdMap $ F Exp [t, G t']]
loadExp pos _ _ = fail (shows pos "Malformed exp")

loadBase :: Monad m => [Term] -> SExpr Pos -> m Term
loadBase vars x =
  do
    t <- loadTerm vars x
    case t of
      F Base [t] -> return t
      _ -> fail (shows (annotation x) "Malformed base")

loadExpn :: Monad m => [Term] -> SExpr Pos -> m Group
loadExpn vars x =
  do
    t <- loadTerm vars x
    case t of
      G t -> return t
      _ -> fail (shows (annotation x) "Malformed expn")

loadOne :: Monad m => LoadFunction m
loadOne _ _ [] =
  return $ G M.empty
loadOne pos _ _ = fail (shows pos "Malformed one")

loadRec :: Monad m => LoadFunction m
loadRec _ vars [x] =
  do
    t <- loadExpn vars x
    return $ G $ invert t
loadRec pos _ _ = fail (shows pos "Malformed rec")

loadMul :: Monad m => LoadFunction m
loadMul _ vars xs =
  do
    t <- foldM f M.empty xs
    return $ G t
  where
    f acc x =
      do
        t <- loadExpn vars x
        return $ mul t acc

-- Term constructors: cat enc

loadCat :: Monad m => LoadFunction m
loadCat _ vars (l : ls) =
  do
    ts <- mapM (loadTerm vars) (l : ls)
    return $ foldr1 (\a b -> F Cat [a, b]) ts
loadCat pos _ _ = fail (shows pos "Malformed cat")

loadEnc :: Monad m => LoadFunction m
loadEnc pos vars (l : l' : ls) =
  do
    let (butLast, last) = splitLast l (l' : ls)
    t <- loadCat pos vars butLast
    t' <- loadTerm vars last
    return $ F Enc [t, t']
loadEnc pos _ _ = fail (shows pos "Malformed enc")

splitLast :: a -> [a] -> ([a], a)
splitLast x xs =
  loop [] x xs
  where
    loop z x [] = (reverse z, x)
    loop z x (y : ys) = loop (x : z) y ys

-- Term specific displaying functions

newtype Context = Context [(Id, String)] deriving Show

displayVars :: Context -> [Term] -> [SExpr ()]
displayVars _ [] = []
displayVars ctx vars =
  let (v,t):pairs = map (displayVar ctx) vars in
  loop t [v] pairs
  where
    loop t vs [] = [L () (reverse (t:vs))]
    loop t vs ((v',t'):xs)
      | t == t' = loop t (v':vs) xs
      | otherwise = L () (reverse (t:vs)):loop t' [v'] xs

displayVar :: Context -> Term -> (SExpr (), SExpr ())
displayVar ctx (I x) = displaySortId "mesg" ctx x
displayVar ctx (F Text [I x]) = displaySortId "text" ctx x
displayVar ctx (F Data [I x]) = displaySortId "data" ctx x
displayVar ctx (F Name [I x]) = displaySortId "name" ctx x
displayVar ctx (F Skey [I x]) = displaySortId "skey" ctx x
displayVar ctx (F Akey [I x]) = displaySortId "akey" ctx x
displayVar ctx (F Base [I x]) = displaySortId "base" ctx x
displayVar ctx t@(G x)
  | isBasisVar x = displaySortId "elem" ctx (varId t)
  | isGroupVar x = displaySortId "expn" ctx (varId t)
displayVar _ _ =
  error "Algebra.displayVar: term not a variable with its sort"

displaySortId :: String -> Context -> Id -> (SExpr (), SExpr ())
displaySortId sort ctx x = (displayId ctx x, S () sort)

displayId :: Context -> Id -> SExpr ()
displayId (Context ctx) x =
  case lookup x ctx of
    Nothing ->
      let msg = idName x ++ " in a display context" in
      error $ "Algebra.displayId: Cannot find variable " ++ msg
    Just name -> S () name

displayTerm :: Context -> Term -> SExpr ()
displayTerm ctx (I x) = displayId ctx x
displayTerm ctx (F Text [I x]) = displayId ctx x
displayTerm ctx (F Data [I x]) = displayId ctx x
displayTerm ctx (F Name [I x]) = displayId ctx x
displayTerm ctx (F Skey [I x]) = displayId ctx x
displayTerm ctx (F Skey [F Ltk [I x, I y]]) =
  L () [S () "ltk", displayId ctx x, displayId ctx y]
displayTerm ctx (F Akey [t]) =
  case t of
    I x -> displayId ctx x
    F Invk [I x] -> L () [S () "invk", displayId ctx x]
    F Pubk [I x] -> L () [S () "pubk", displayId ctx x]
    F Pubk [C c, I x] -> L () [S () "pubk", Q () c, displayId ctx x]
    F Invk [F Pubk [I x]] -> L () [S () "privk", displayId ctx x]
    F Invk [F Pubk [C c, I x]] ->
      L () [S () "privk", Q () c, displayId ctx x]
    _ -> error ("Algebra.displayAkey: Bad term " ++ show t)
displayTerm ctx (F Base [t]) =
  displayBase t
  where
    displayBase (I x) = displayId ctx x
    displayBase (F Genr []) =
      L () [S () "gen"]
    displayBase (F Exp [t0, G t1]) =
      L () [S () "exp", displayBase t0, displayTerm ctx (G t1)]
    displayBase t = error ("Algebra.displayBase: Bad term " ++ show t)
displayTerm ctx (G t) =
  displayExpn t
  where
    displayExpn t
      | M.null t = L () [S () "one"]
      | otherwise =
        case factors t of
          [f] -> displayFactor f
          fs -> L () (S () "mul" : map displayFactor fs)
    displayFactor (x, n)
      | n >= 0 = displayId ctx x
      | otherwise = L () [S () "rec", displayId ctx x]
displayTerm _ (C t) = Q () t
displayTerm ctx (F Cat [t0, t1]) =
  L () (S () "cat" : displayTerm ctx t0 : displayList ctx t1)
displayTerm ctx (F Enc [t0, t1]) =
  L () (S () "enc" : displayEnc ctx t0 t1)
displayTerm _ t = error ("Algebra.displayTerm: Bad term " ++ show t)

displayList :: Context -> Term -> [SExpr ()]
displayList ctx (F Cat [t0, t1]) = displayTerm ctx t0 : displayList ctx t1
displayList ctx t = [displayTerm ctx t]

displayEnc :: Context -> Term -> Term -> [SExpr ()]
displayEnc ctx (F Cat [t0, t1]) t = displayTerm ctx t0 : displayEnc ctx t1 t
displayEnc ctx t0 t1 = [displayTerm ctx t0, displayTerm ctx t1]

displayEnv :: Context -> Context -> Env -> [SExpr ()]
displayEnv ctx ctx' (Env (_, r)) =
  map (\(x, t) -> L () [displayTerm ctx x, displayTerm ctx' t]) r'
  where
    r' = map (\(x, t) -> (I x, inferSort t)) $ M.assocs r

factors :: Group -> [(Id, Int)]
factors t =
  do
    (x, (_, n)) <- M.assocs t
    case n >= 0 of
      True -> replicate n (x, 1)
      False -> replicate (negate n) (x, -1)

-- displaySubst c s displays a substitution s in context c, where some
-- variables that occur in s might not be in c.  Enough sort
-- inference is performed so as to allow the extension of the context.
displaySubst :: Context -> Subst -> [SExpr ()]
displaySubst ctx s@(Subst r) =
  map (\(x, t) -> L () [displayTerm ctx' x, displayTerm ctx' t]) r'
  where
    r' = map (\(x, t) -> (I x, inferSort (substitute s t))) $ M.assocs r
    ctx' = foldl (\ctx (x, t) -> addToContext ctx [x, t]) ctx r'

inferSort :: Term -> Term
inferSort t@(F Invk _) = F Akey [t]
inferSort t@(F Pubk _) = F Akey [t]
inferSort t@(F Ltk _) = F Skey [t]
inferSort t@(F Genr _) = F Base [t]
inferSort t@(F Exp _) = F Base [t]
inferSort t = t

emptyContext :: Context
emptyContext = Context []

-- Generate names for output renaming as necessary.
-- Assumes the input is a list of term that are well-formed
addToContext :: Context -> [Term] -> Context
addToContext ctx u =
  foldl (foldVars varContext) ctx u

varContext :: Context -> Term -> Context
varContext ctx t =
  let x = varId t
      name = rootName $ idName x in
  if hasId ctx x then
    ctx
  else
    if hasName ctx name then
      extendContext ctx x (genName ctx name)
    else
      extendContext ctx x name

hasId :: Context -> Id -> Bool
hasId (Context ctx) id =
  maybe False (const True) (lookup id ctx)

hasName :: Context -> String -> Bool
hasName (Context ctx) name =
  maybe False (const True) (L.find ((name ==) . snd) ctx)

extendContext :: Context -> Id -> String -> Context
extendContext (Context ctx) x name =
  Context $ (x, name) : ctx

genName :: Context -> String -> String
genName ctx name =
  loop 0
  where
    root = '-' : reverse name
    loop :: Int -> String
    loop n =
      let name' = revapp root (show n) in
      if hasName ctx name' then
        loop (n + 1)
      else
        name'
    revapp [] s = s
    revapp (c : cs) s = revapp cs (c : s)

rootName :: String -> String
rootName name =
  noHyphen 0 name
  where
    noHyphen _ [] = name
    noHyphen i (c : s)
      | c == '-' = hyphen i (i + 1) s
      | otherwise = noHyphen (i + 1) s
    hyphen i _ [] = rootName $ take i name
    hyphen i j (c : s)
      | isDigit c  = hyphen i (j + 1) s
      | otherwise = noHyphen j (c : s)

instance C.Context Term Gen Subst Env Context where
  emptyContext = emptyContext
  addToContext = addToContext
  displayVars = displayVars
  displayTerm = displayTerm
  displayEnv = displayEnv
  displaySubst = displaySubst

instance C.Algebra Term Place Gen Subst Env Context
