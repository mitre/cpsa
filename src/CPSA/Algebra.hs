-- Diffie-Hellman Algebra implementation

-- This module implements a version of Diffie-Hellman in which
-- exponents form a free Abelian group.  It uses the basis elements as
-- atoms principle.

-- To support security goals, the message algebra has been augmented
-- with support for variables of sort node and pairs of integers.  The
-- constructor D is used as N is taken for numbers in S-Expressions.

-- Copyright (c) 2021 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

--------------------------------------------------------------------

-- The module implements a many-sorted algebra, but is used as an
-- order-sorted algebra.  It exports a name, and the origin used to
-- generate variables.

-- The Diffie-Hellman Order-Sorted Signature is

-- Sorts: mesg, text, data, name, skey, akey, tag,
--        string, base, expt, and rndx
--
-- Subsorts: text, data, name, skey, akey,
--           base, expt < mesg and rndx < expt
--
-- Operations:
--   cat : mesg X mesg -> mesg               Pairing
--   enc : mesg X mesg -> mesg               Encryption
--   hash : mesg -> mesg                     Hashing
--   string : mesg                           Tag constants
--   ltk : name X name -> skey               Long term shared key
--   bltk : name X name -> skey              Bidirectional long-term key
--   pubk : name -> akey                     Public key of principal
--   pubk : string X name -> akey            Tagged public key of principal
--   invk : akey -> akey                     Inverse of asymmetric key
--   gen : base                              DH generator
--   exp : base X expt -> base               Exponentiation
--   mul : expt X expt -> expt               Group operation
--   rec : expt -> expt                      Group inverse
--   one : expt                              Group identity
--
-- Atoms: messages of sort text, data, name, skey, akey, and rndx, and
--        messages of the form (exp (gen) x) where x is of sort rndx.

-- A free Abelian group has a set of basis elements, and the sort rndx
-- is the sort for basis elements.  Limiting the atoms associated with
-- an exponent to basis elements is the basis elements as atoms
-- principle.  This principle enables CPSA to correctly handle
-- origination assumptions.

-- The implementation exploits the isomorphism between order-sorted
-- algebras and many-sorted algebras by adding inclusion operations to
-- produce an equivalent Diffie-Hellman Many-Sorted Signature.  There
-- is an inclusion operation for each subsort of mesg.  Diffie-Hellman
-- exponents are handled specially using a canonical representation as
-- monomials.

-- Sorts: mesg, text, data, name, skey, akey,
--        string, base, expt, and rndx
--
-- Operations:
--   cat : mesg X mesg -> mesg               Pairing
--   enc : mesg X mesg -> mesg               Encryption
--   hash : mesg -> mesg                     Hashing
--   string : mesg                           Tag constants
--   ltk : name X name -> skey               Long term shared key
--   bltk : name X name -> skey              Bidirectional long-term key
--   pubk : name -> akey                     Public key of principal
--   pubk : string X name -> akey            Tagged public key of principal
--   invk : akey -> akey                     Inverse of asymmetric key
--   text : text -> mesg                     Sort text inclusion
--   data : data -> mesg                     Sort date inclusion
--   name : name -> mesg                     Sort name inclusion
--   skey : skey -> mesg                     Sort skey inclusion
--   akey : akey -> mesg                     Sort akey inclusion
--   base : base -> mesg                     Sort base inclusion
--
--  A message of sort expt, a monomial, is represented by a map from
--  identifiers to descriptions.  A description is a pair consisting
--  of a flag saying if the variable is of sort rndx or expt, and a
--  non-zero integer.  For t of sort expt, the monomial associated
--  with t is
--
--      x1 ^ c1 * x2 ^ c2 * ... * xn ^ cn
--
-- for all xi in the domain of t and t(xi) = (_, ci).

-- In both algebras, invk(invk(t)) = t for all t of sort akey,
-- (exp h (one)) = h, (exp (exp h x) y) = (exp h (mul x y)), and
-- the Abelian group axioms hold.

{-# LANGUAGE CPP #-}

#define CHECK_CANONICAL

module CPSA.Algebra (name, alias,

    Gen,
    origin,
    gmerge,
    clone,
    loadVars,
    basePrecursor,
    newVar,
    newVarDefault, 
    varName,

    Term,
    isVar,
    isAcquiredVar,
    isObtainedVar,
    isAtom,
    isStrdVar,
    isChan,
    isLocn,
    isIndxVar,
    isIndxConst,
    termsWellFormed,
    occursIn,
    foldVars,
    foldCarriedTerms,
    carriedBy,
    constituent,
    decryptionKey,
    decompose,
    buildable,
    components,
    encryptions,
    escapeSet,
    loadTerm,
    loadLocnTerm,
    indxOfInt,
    isNum,
    subNums,
    consts,
    isBase,
    isExpr,
    isVarExpr,
    isRndx,
    exprVars,

    Place (..),
    places,
    carriedPlaces,
    carriedRelPlaces,
    replace,
    ancestors,
    placeIsPrefixOf,
    placeStripPrefix,

    Subst,
    emptySubst,
    destroyer,
    disjointDom,
    substitute,
    unify,
    compose,
    absentSubst,

    Env,
    emptyEnv,
    instantiate,
    matched,
    match,
    substitution,
    strandBoundEnv,
    reify,
    substUpdate,
    strdMatch,
    strdLookup,
    strdUpdate,
    indxLookup,
    indxUpdate,

    isLocnMsg,
    locnMsgPayload,
    locnMsgPoint,

    Context,
    emptyContext,
    addToContext,
    displayVars,
    displayTerm,
    displayTermNoPt,
    notPt,
    displayEnv,
    displaySubst,
    varListSpecOfVars) where

import Control.Monad -- (foldM)
import qualified Data.List as L
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M
import Data.Map (Map)
import Data.Char (isDigit)
import CPSA.Lib.Utilities (replaceNth, adjoin, assertError)
import CPSA.Lib.SExpr (SExpr(..), Pos, annotation)
import CPSA.Signature (Sig)
import qualified CPSA.Signature as Sig

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

-- The default name for the algebra handled by this module
-- One gets Diffie Hellman features too.
name :: String
name = "basic"

-- The name used when Diffie Hellman features are explictly requested
alias :: String
alias = "diffie-hellman"

-- An identifier is a variable without any information about its sort

newtype Id = Id (Integer, String) deriving Show

-- The integer distinguishes an identifier, the string is for printing.

instance Eq Id where
    (Id (x, _)) == (Id (x', _)) = x == x'

instance Ord Id where
    compare (Id (x, _)) (Id (x', _)) = compare x x'

idName :: Id -> String
idName (Id (_, name)) = name

-- Counter used for generating fresh identifiers.

newtype Gen = Gen (Integer) deriving (Show, Eq)

origin :: Gen
origin = Gen (0)

gmerge :: Gen -> Gen -> Gen
gmerge (Gen i) (Gen j) = Gen $ max i j

freshId :: Gen -> String -> (Gen, Id)
freshId (Gen i) name = (Gen (i + 1), Id (i, name))

cloneId :: Gen -> Id -> (Gen, Id)
cloneId gen x = freshId gen (idName x)

-- A term in an Abelian group is a map from identifiers to pairs of
-- sorts and non-zero integers.

data Sort
  = Rndx                        -- Sort of a basis element
  | Expt
  deriving (Show, Eq, Ord)

type Coef = Int

type Desc = (Sort, Coef)

type Group = Map Id Desc

isGroupVar :: Group -> Bool
isGroupVar t =
  M.size t == 1 && snd (head (M.elems t)) == 1

isBasisVar :: Group -> Bool
isBasisVar t =
  M.size t == 1 && head (M.elems t) == (Rndx, 1)

isExprVar :: Group -> Bool
isExprVar t =
  M.size t == 1 && head (M.elems t) == (Expt, 1)

-- Assumes isGroupVar t, isBasisVar t, or isExprVar is True!
getGroupVar :: Group -> Id
getGroupVar x = head $ M.keys x

-- Create group var as a basis element if be is Rndx
groupVarG :: Sort -> Id -> Group
groupVarG be x = M.singleton x (be, 1)

groupVar :: Sort -> Id -> Term
groupVar be x = G $ groupVarG be x

groupVarGroup :: Id -> Group
groupVarGroup x = groupVarG Expt x

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
      | b /= b' = assertError
        ("Algebra.mul: sort mismatch " ++ show t ++ " - " ++ show t')
      | c + c' == 0 = Nothing          -- Delete the mapping
      | otherwise = Just $ (b, c + c') -- Adjust the mapping

-- Why not replace M.assocs with M.toList elsewhere?

type Maplet = (Id, Desc)

mMapCoef :: (Coef -> Coef) -> Maplet -> Maplet
mMapCoef f (x, (be, c)) = (x, (be, f c))

mInverse :: [Maplet] -> [Maplet]
mInverse maplets = map (mMapCoef negate) maplets

isMapletNonzero :: Maplet -> Bool
isMapletNonzero (_, (_, c)) = c /= 0

group :: [Maplet] -> Group
group maplets =
  M.fromList $ filter isMapletNonzero maplets

exprVars :: Term -> [Term]
exprVars (G g) =
  M.foldlWithKey f [] g
  where
    f vars id (sort, _) = groupVar sort id : vars
exprVars t = error ("Algebra.exprVars: Expecting exponent but got " ++ show t)

-- For Absence

-- Seperate a group term based on one variable.
-- When the variable is not in the group, return Nothing
-- Otherwise return a group with just the variable negated,
-- and a group that contains the rest of the group.
separateVar :: Id -> Group -> Maybe (Group, Group)
separateVar var t =
  case M.lookup var t of
    Nothing -> Nothing
    Just (basis, coef) ->
      Just (M.singleton var (basis, negate coef),
            M.delete var t)

-- Operations other than the tag constant constructor
data Symbol
    = Data String               -- Atoms
    | Akey String               -- Asymmetric keys
    | Name                      -- Principal
    | Pval                      -- Point at which a store occurs
    | Base                      -- Base of an exponentiated atom
    | Ltk                       -- Long term shared symmetric key
    | Bltk                      -- Bidirectional ltk
    | Invk String               -- Inverse of asymmetric key
    | Pubk                      -- Public asymmetric key of a principal
    | Chan                      -- Channel
    | Locn                      -- Location
    | Genr                      -- The generator constant for the group
    | Exp                       -- Exponentiation function symbol
    | Tupl String               -- Term tupling
    | Enc String                -- Encryption
    | Hash String               -- Hashing
      deriving (Show, Eq, Ord)

-- A Basic Crypto Algebra Term

data Term
    = I !Id
    | C !String                 -- Tag constants
    | F !Symbol ![Term]
    | G !Group                  -- An exponent, an Abelian group
    | D !Id                     -- Strd variable
    | Z Int                     -- Strd constant
    | X !Id                     -- Indx variable
    | Y Int                     -- Indx constant
#if !defined CHECK_CANONICAL
      deriving (Show, Eq, Ord)
#else
      deriving Show

equalTerm :: Term -> Term -> Bool
equalTerm (I x) (I y) = x == y
equalTerm (C c) (C c') = c == c'
equalTerm (G t) (G t') = t == t'
#if defined CHECK_CANONICAL
equalTerm l@(F (Invk _) [F (Invk _) [_]]) _ = error ("EQ: " ++ show l)
equalTerm _ l@(F (Invk _) [F (Invk _) [_]]) = error ("EQ: " ++ show l)
equalTerm l@(F Exp [_, G t1]) _ | M.null t1 = error ("EQ: " ++ show l)
equalTerm _ l@(F Exp [_, G t1]) | M.null t1 = error ("EQ: " ++ show l)
equalTerm l@(F Exp [F Exp [_, G _], G _]) _ = error ("EQ: " ++ show l)
equalTerm _ l@(F Exp [F Exp [_, G _], G _])  = error ("EQ: " ++ show l)
#else
-- equalTerm (F (Invk op) [F (Invk op') [t]]) t' | op == op' = equalTerm t t'
-- equalTerm t (F (Invk op) [F (Invk op') [t']]) | op == op' = equalTerm t t'
equalTerm (F (Invk _) [F (Invk _) [t]]) t' = equalTerm t t'
equalTerm t (F (Invk _) [F (Invk _) [t']]) = equalTerm t t'
equalTerm (F Exp [t0, G t1]) t' | M.null t1 = equalTerm t0 t'
equalTerm t (F Exp [t0, G t1]) | M.null t1 = equalTerm t t0
equalTerm (F Exp [F Exp [t, G t0], G t1]) t' =
    equalTerm (F Exp [t, G (mul t0 t1)]) t'
equalTerm t (F Exp [F Exp [t', G t0], G t1])  =
    equalTerm t (F Exp [t', G (mul t0 t1)])
#endif
equalTerm (F Bltk [t0, t1]) (F Bltk [t0', t1']) =
    (equalTerm t0 t0' && equalTerm t1 t1') ||
    (equalTerm t0 t1' && equalTerm t1 t0')
equalTerm (F s u) (F s' u') =
    s == s' && equalTermLists u u'
equalTerm (D x) (D y) = x == y
equalTerm (Z p) (Z p') = p == p'
equalTerm (X x) (X y) = x == y
equalTerm (Y x) (Y y) = x == y
equalTerm _ _ = False

equalTermLists :: [Term] -> [Term] -> Bool
equalTermLists [] [] = True
equalTermLists (t : u) (t' : u') =
    equalTerm t t' && equalTermLists u u'
equalTermLists _ _ = False

instance Eq Term where
    (==) = equalTerm

-- Term comparison respecting the axiom X

compareTerm :: Term -> Term -> Ordering
compareTerm (I x) (I y) = compare x y
compareTerm (C c) (C c') = compare c c'
compareTerm (G t) (G t') = compare t t'
#if defined CHECK_CANONICAL
compareTerm l@(F (Invk _) [F (Invk _) [_]]) _ = error ("COM: " ++ show l)
compareTerm _ l@(F (Invk _) [F (Invk _) [_]]) = error ("COM: " ++ show l)
compareTerm l@(F Exp [_, G t1]) _ | M.null t1 = error ("COM: " ++ show l)
compareTerm _ l@(F Exp [_, G t1]) | M.null t1 = error ("COM: " ++ show l)
compareTerm l@(F Exp [F Exp [_, G _], G _]) _ = error ("COM: " ++ show l)
compareTerm _ l@(F Exp [F Exp [_, G _], G _]) = error ("COM: " ++ show l)
#else
compareTerm (F (Invk _) [F (Invk _) [t]]) t' = compareTerm t t'
compareTerm t (F (Invk _) [F (Invk _) [t']]) = compareTerm t t'
compareTerm (F Exp [t0, G t1]) t' | M.null t1 = compareTerm t0 t'
compareTerm t (F Exp [t0, G t1]) | M.null t1 = compareTerm t t0
compareTerm (F Exp [F Exp [t, G t0], G t1]) t' =
    compareTerm (F Exp [t, G (mul t0 t1)]) t'
compareTerm t (F Exp [F Exp [t', G t0], G t1])  =
    compareTerm t (F Exp [t', G (mul t0 t1)])
#endif
compareTerm (F Bltk [t0, t1]) (F Bltk [t0', t1']) =
    if compareTerm t0 t1 == GT then
      compareTerm (F Bltk [t1, t0]) (F Bltk [t0', t1'])
    else if compareTerm t0' t1' == GT then
           compareTerm (F Bltk [t0,t1]) (F Bltk [t1', t0'])
         else compareTermLists [t0, t1] [t0', t1']
compareTerm (F s u) (F s' u') =
    case compare s s' of
      EQ -> compareTermLists u u'
      o -> o
compareTerm (D x) (D y) = compare x y
compareTerm (Z p) (Z p') = compare p p'
compareTerm (X x) (X y) = compare x y
compareTerm (Y x) (Y y) = compare x y
compareTerm (I _) (C _) = LT
compareTerm (C _) (I _) = GT
compareTerm (I _) (F _ _) = LT
compareTerm (F _ _) (I _) = GT
compareTerm (I _) (G _) = LT
compareTerm (G _) (I _) = GT
compareTerm (I _) (D _) = LT
compareTerm (D _) (I _) = GT
compareTerm (I _) (Z _) = LT
compareTerm (Z _) (I _) = GT
compareTerm (C _) (F _ _) = LT
compareTerm (F _ _) (C _) = GT
compareTerm (C _) (G _) = LT
compareTerm (G _) (C _) = GT
compareTerm (C _) (D _) = LT
compareTerm (D _) (C _) = GT
compareTerm (C _) (Z _) = LT
compareTerm (Z _) (C _) = GT
compareTerm (F _ _) (G _) = LT
compareTerm (G _) (F _ _) = GT
compareTerm (F _ _) (D _) = LT
compareTerm (D _) (F _ _) = GT
compareTerm (F _ _) (Z _) = LT
compareTerm (Z _) (F _ _) = GT
compareTerm (G _) (D _) = LT
compareTerm (D _) (G _) = GT
compareTerm (G _) (Z _) = LT
compareTerm (Z _) (G _) = GT
compareTerm (D _) (Z _) = LT
compareTerm (Z _) (D _) = GT
compareTerm (X _) (Y _) = LT
compareTerm (Y _) (X _) = GT
compareTerm (X _) _ = GT
compareTerm _ (X _) = LT
compareTerm (Y _) _ = GT
compareTerm _ (Y _) = LT

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
#endif

-- Basic terms are introduced by defining a function used to decide if
-- a term is well-formed.  The context of an occurrence of an identifier
-- determines its sort.  A term that contains just an identifier and its
-- sort information is called a variable.  The sort of a variable is
-- one of mesg, text, data, name, skey, and akey.

-- Terms that represent algebra variables.
isVar :: Term -> Bool
isVar (I _) = True           -- Sort: mesg
isVar (F s [I _]) = varSym s
isVar (G t) = isGroupVar t
isVar _ = False

varSym :: Symbol -> Bool
varSym (Data _) = True
varSym (Akey _) = True
varSym Name = True
varSym Pval = True
varSym Base = True
varSym Chan = True
varSym Locn = True
varSym _ = False

-- Is term a channel variable
isChan :: Term -> Bool
isChan (F Chan [I _]) = True
isChan _ = False

-- Is term a location variable
isLocn :: Term -> Bool
isLocn (F Locn [I _]) = True
isLocn _ = False

-- Note that isVar of (D _) is false.
isStrdVar :: Term -> Bool
isStrdVar (D _) = True
isStrdVar _ = False

-- Note that isVar of (X _) is false.
isIndxVar :: Term -> Bool
isIndxVar (X _) = True
isIndxVar _ = False

isIndxConst :: Term -> Bool
isIndxConst (Y _) = True
isIndxConst _ = False

-- Extract the identifier from a variable
varId :: Term -> Id
varId (I x) = x
varId (F (Data _) [I x]) = x
varId (F (Akey _) [I x]) = x
varId (F Name [I x]) = x
varId (F Base [I x]) = x
varId (F Pval [I x]) = x
varId (F Chan [I x]) = x
varId (F Locn [I x]) = x
varId (G g) = getGroupVar g
varId (D x) = x
varId (X x) = x
varId _ = error "Algebra.varId: term not a variable with its sort"

isAcquiredVar :: Term -> Bool
isAcquiredVar (I _) = True
isAcquiredVar _ = False

isObtainedVar :: Term -> Bool
isObtainedVar (G x) = isExprVar x
isObtainedVar (F Base [I _]) = True
isObtainedVar _ = False

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

-- termWellFormed checks the structure and sort condition.

termWellFormed :: VarEnv -> Term -> Maybe VarEnv
termWellFormed xts t@(I x) =
    extendVarEnv xts x t        -- Mesg variable
termWellFormed xts t@(F (Data _) [I x]) =
    extendVarEnv xts x t        -- Data variable
termWellFormed xts (F (Data "skey") [F Ltk [I x, I y]]) =
                                -- Long term shared symmetric key
    foldM termWellFormed xts [F Name [I x], F Name [I y]]
termWellFormed xts (F (Data "skey") [F Bltk [I x, I y]]) =
                                -- Long term shared symmetric key
    foldM termWellFormed xts [F Name [I x], F Name [I y]]
termWellFormed xts (F (Akey op) [t]) = -- Asymmetric key terms
    case t of
      I x -> extendVarEnv xts x (F (Akey op) [I x])
      F (Invk op') [I x]
        | op' == op -> extendVarEnv xts x (F (Akey op) [I x])
      F Pubk [I x]
        | op == "akey" -> extendVarEnv xts x (F Name [I x])
      F Pubk [C _, I x]
        | op == "akey" -> extendVarEnv xts x (F Name [I x])
      F (Invk "akey") [F Pubk [I x]]
        | op == "akey" -> extendVarEnv xts x (F Name [I x])
      F (Invk "akey") [F Pubk [C _, I x]]
        | op == "akey" -> extendVarEnv xts x (F Name [I x])
      _ -> Nothing
termWellFormed xts t@(F Name [I x]) =
    extendVarEnv xts x t        -- Name variable
termWellFormed xts t@(F Pval [I x]) =
    extendVarEnv xts x t        -- pval variable
termWellFormed xts (F Base [t]) =
    baseVarEnv xts t
    where
      baseVarEnv xts t@(I x) =
          extendVarEnv xts x (F Base [t])
      baseVarEnv xts (F Genr []) =
          Just xts
      -- Check for non-canonical form
      baseVarEnv _ (F Exp [F Exp _, _]) = Nothing
      baseVarEnv xts (F Exp [t0, G t1]) =
          do
            xts <- baseVarEnv xts t0
            termWellFormed xts (G t1)
      baseVarEnv _ _ = Nothing
termWellFormed xts (G t) =
    foldM rndxVarEnv xts (M.assocs t)
    where
      rndxVarEnv xts (x, (be, _)) =
          extendVarEnv xts x (groupVar be x)
termWellFormed xts (C _) =
    Just xts                    -- Tags
termWellFormed xts (F (Tupl _) ts) =
    foldM termWellFormed xts ts -- Tupling
termWellFormed xts (F (Enc _) ts@[_, _]) =
    foldM termWellFormed xts ts  -- Encryption
termWellFormed xts (F (Hash _) [t])     =
    termWellFormed xts t            -- Hashing
termWellFormed _ _ = Nothing

-- Extend when sorts agree
extendVarEnv :: VarEnv -> Id -> Term -> Maybe VarEnv
extendVarEnv (VarEnv env) x t =
    case M.lookup x env of
      Nothing -> Just $ VarEnv $ M.insert x t env
      Just t' -> if t == t' then Just (VarEnv env) else Nothing

-- Is the sort of the term a base sort?
isAtom :: Term -> Bool
isAtom (F Base _) = False
isAtom (F s _) = varSym s
isAtom (G x) = isBasisVar x
isAtom _ = False

-- Is the term numeric?
isNum :: Term -> Bool
isNum (F Base _) = True
isNum (G _) = True
isNum _ = False

subNums :: Term -> Set Term
subNums t@(G _) = S.singleton t
subNums (F _ ts) = S.unions (map subNums ts)
subNums _ = S.empty

-- Does a variable occur in a term?
occursIn :: Term -> Term -> Bool
occursIn t t' | isVar t =
  subterm (I $ varId t) t'
occursIn t _ =
  error $ "Algebra.occursIn: Bad variable " ++ show t

subterm :: Term -> Term -> Bool
subterm t t' | t == t' =
  True
subterm t (F _ u) =
  any (subterm t) u
subterm (I x) (G t') =
  M.member x t'
subterm (G t) (G t') | isBasisVar t = -- For constituent
  M.member (getGroupVar t) t'
subterm _ _ = False

-- Fold f through a term applying it to each variable in the term.
foldVars :: (a -> Term -> a) -> a -> Term -> a
foldVars f acc t@(I _) = f acc t          -- Mesg variable
foldVars f acc t@(F (Data _) [I _]) = f acc t -- Data variable
foldVars f acc (F (Data _) [F Ltk [I x, I y]]) =
    f (f acc (F Name [I x])) (F Name [I y])
foldVars f acc (F (Data _) [F Bltk [I x, I y]]) =
    f (f acc (F Name [I x])) (F Name [I y])
foldVars f acc t@(F (Akey _) [I _]) = f acc t -- Asymmetric keys
foldVars f acc (F op@(Akey _) [F (Invk _) [I x]]) = f acc (F op [I x])
foldVars f acc (F (Akey _) [F Pubk [I x]]) = f acc (F Name [I x])
foldVars f acc (F (Akey _) [F Pubk [C _, I x]]) = f acc (F Name [I x])
foldVars f acc (F (Akey _) [F (Invk _) [F Pubk [I x]]]) =
  f acc (F Name [I x])
foldVars f acc (F (Akey _) [F (Invk _) [F Pubk [C _, I x]]]) =
  f acc (F Name [I x])
foldVars f acc t@(F Name [I _]) = f acc t -- Name variable
foldVars f acc t@(F Pval [I _]) = f acc t -- Pval variable
foldVars f acc t@(F Chan [I _]) = f acc t -- Channels
foldVars f acc t@(F Locn [I _]) = f acc t -- Locn
foldVars f acc (F Base [t]) =
    baseAddVars acc t
    where
      baseAddVars acc t@(I _) =
          f acc (F Base [t])
      baseAddVars acc (F Genr []) =
          acc
      baseAddVars acc (F Exp [t0, G t1]) =
          foldVars f (baseAddVars acc t0) (G t1)
      baseAddVars _ _ = assertError "Algebra.foldVars: Bad term"
foldVars f acc (G t) =
    M.foldlWithKey rndxAddVars acc t
    where
      rndxAddVars acc x (be, _) =
          f acc (groupVar be x)
foldVars _ acc (C _) = acc                    -- Tags
foldVars f acc (F (Tupl _) ts) =              -- Concatenation
    foldl (foldVars f) acc ts
foldVars f acc (F (Enc _) [t0, t1]) =         -- Encryption
    foldVars f (foldVars f acc t0) t1
foldVars f acc (F (Hash _) [t]) =             -- Hashing
    foldVars f acc t
foldVars f acc t@(D _) = f acc t          -- Strd variable
foldVars _ acc (Z _) = acc                -- Strd constant
foldVars f acc t@(X _) = f acc t          -- Indx variable
foldVars _ acc (Y _) = acc                -- Indx constant
foldVars _ _ t = error $ "Algebra.foldVars: Bad term " ++ show t

-- Fold f through a term applying it to each term that is carried by the term.
foldCarriedTerms :: (a -> Term -> a) -> a -> Term -> a
foldCarriedTerms f acc t@(F (Tupl _) ts) = -- Concatenation
    foldl (foldCarriedTerms f) (f acc t) ts
foldCarriedTerms f acc t@(F (Enc _) [t0, _]) = -- Encryption
    foldCarriedTerms f (f acc t) t0
--foldCarriedTerms f acc t@(F Base [F Exp [_, t1]]) = -- Exponents
--    f (f acc t) t1
foldCarriedTerms f acc t = f acc t     -- atoms and tags

-- Is a term carried by another term?
carriedBy :: Term -> Term -> Bool
carriedBy t t' =
    t == t' ||
      case t' of
        F (Tupl _) ts -> any (carriedBy t) ts
        F (Enc _) [t0, _] -> carriedBy t t0
        _ -> False

-- Is atom a constituent of a term?  In other words, is atom among
-- the set of atoms required to construct the term?
constituent :: Term -> Term -> Bool
constituent t t' | isAtom t =
  subterm t t'
constituent t _ =
  error $ "Algebra.constituent: Bad atom " ++ show t

-- The key used to decrypt an encrypted term, otherwise Nothing.
decryptionKey :: Term -> Maybe Term
decryptionKey (F (Enc _) [_, t]) = Just (inv t)
decryptionKey _ = Nothing

buildable :: Set Term -> Set Term -> Term -> Bool
buildable knowns unguessable term =
    ba term
    where
      ba (I _) = True           -- A mesg sorted variable is always buildable
      ba (C _) = True           -- So is a tag
      ba (F (Tupl _) ts) =
          all ba ts
      ba t@(F (Enc _) [t0, t1]) =
          S.member t knowns || ba t0 && ba t1
      ba t@(F (Hash _) [t1]) =
          S.member t knowns || ba t1
      ba t@(F Base _) = bb t
      ba (G t1) = be t1
      ba t = isAtom t && not (S.member t unguessable)
      -- Buildable base term
      bb (F Base [I _]) = True           -- A variable of sort base is always buildable
      bb (F Base [F Genr _]) = True     -- and so is the generator
      bb t@(F Base [F Exp [t0, G t1]]) =
        any (\t2 -> (getBase t2 == t0) && relevant unguessable t2 t)
           (S.toList knowns) || bb (F Base [t0]) && be t1
      bb (_) = False
      -- Buildable exponent
      be exp =
        all (flip notElem ids) $ M.keys exp
      -- Exponent variables with origination assumptions
      ids = getRndxOrigAssumptions unguessable
      -- Known exponent without non-known variables
      -- kns = map (stripRndx ids) (getRndxs knowns)

getRndxOrigAssumptions :: Set Term -> [Id]
getRndxOrigAssumptions terms =
    concatMap f $ S.elems terms
    where
      f (G t) = M.keys t        -- This is an approximation
      f _ = []

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
      loop unguessable knowns old (t@(F (Tupl _) _) : todo) =
          loop unguessable (decat t (S.delete t knowns)) old todo
      loop unguessable knowns old ((F (Enc _) [t0, t1]) : todo)
          | buildable knowns unguessable (inv t1) = -- Add plaintext
              loop unguessable (decat t0 knowns) old todo
          | otherwise = loop unguessable knowns old todo
      loop unguessable knowns old ((F (Hash _) [_]) : todo) =
          loop unguessable knowns old todo -- Hash can't be decomposed
      -- New case here: don't delete exponentiated values
      loop unguessable knowns old (F Base [F Exp [_, _]] : todo) =
          loop unguessable knowns old todo
      --  New case here: don't delete exponents that
      -- aren't in unguessable
      loop unguessable knowns old (t@(G _) : todo)
          | S.notMember t unguessable =
              loop unguessable knowns old todo
      loop unguessable knowns old (t : todo) =
          loop (S.delete t unguessable) (S.delete t knowns) old todo
      -- Decat
      decat :: Term -> Set Term -> Set Term
      decat (F (Tupl _) ts) s = foldl (\a b -> decat b a) s ts
      decat t s = S.insert t s

-- Inverts an asymmetric key
inv :: Term -> Term
inv (F (Akey op) [F (Invk _) [t]]) = F (Akey op) [t]
inv (F (Akey op) [t]) = F (Akey op) [F (Invk op) [t]]
inv t@(F _ _) = t
inv t@(G _) = t
inv (I _) = error "Algebra.inv: Cannot invert a variable of sort mesg"
inv (C _) = error "Algebra.inv: Cannot invert a tag constant"
inv (D _) = error "Algebra.inv: Cannot invert a variable of sort strd"
inv (Z _) = error "Algebra.inv: Cannot invert a strd constant"
inv (X _) = error "Algebra.inv: Cannot invert a variable of sort indx"
inv (Y _) = error "Algebra.inv: Cannot invert an indx constant"

components :: Term -> [Term]
components (F (Tupl _) ts) =
    L.nub (L.concat $ map components ts)
components t = [t]

-- Extracts every encryption that is carried by a term along with its
-- encryption key.  Note that a hash is treated as a kind of
-- encryption in which the term that is hashed is the encryption key.
encryptions :: Term -> [(Term, [Term])]
encryptions t =
    reverse $ f t []
    where
      f (F (Tupl _) ts) acc =
        foldl (\a b -> f b a) acc ts
      f t@(F (Enc _) [t', t'']) acc =
        f t' (adjoin (t, [t'']) acc)
      f t@(F (Hash _) [t']) acc =
        adjoin (t, [t']) acc
      f _ acc = acc

-- Put a base expression in the form g, g^e, or b or b^e where b is a variable.
expCollapse :: Term -> Term
expCollapse (F Base [F Genr ts]) = F Base [F Genr ts]
-- expCollapse (F Genr _) = F Base [F Genr []]
expCollapse (F Base [F Exp [F Exp [b, G e0], G e1]]) =
  case expCollapse (F Base [F Exp [b, G e0]]) of
    F Base [F Exp [b', G e0']] -> F Base [F Exp [b', G (mul e0' e1)]]
    _ -> error ("Algebra.hs: expCollapse returned non-base element")
expCollapse (F Base [F Exp [b, G e]]) = F Base [F Exp [b, G e]]
expCollapse (F Base [I t]) = F Base [I t]
expCollapse _ = error ("Algebra.hs: expCollapse called on non-base element")

getBase :: Term -> Term
getBase (F Base [(F Genr _)]) = F Base [F Genr []]
getBase t@(F Base _) =
  case expCollapse t of
    F Base [F Exp [b, _]] -> b
    _ -> t  -- If not exponentiated, the term is the base.
getBase t = t

relevant :: Set Term -> Term -> Term -> Bool
relevant avoid t1@(F Base _) t2@(F Base _) =
    i1 == i2
    where
      i1 = indicator avoid t1
      i2 = indicator avoid t2 -- compare indicators.
relevant _ t1 t2 = t1 == t2

-- Extract the exponent of the term restricted to its map on exponent
-- variables in avoid.
indicator :: Set Term -> Term -> Group
indicator avoid t@(F Base _) =
  case expCollapse t of
    F Base [F Genr _] -> M.empty
    F Base [I _] -> M.empty
    F Base [F Exp [_, G m]] -> M.intersection m indicatorBasis
    _ -> error ("Algebra.hs: expCollapse returned non-base element")
  where
    numAvoid = S.map extrRndx $ S.filter isRndx avoid
    isRndx (G g) = isBasisVar g
    isRndx _ = False
    extrRndx (G t) = t
    extrRndx _ = error ("Algebra.hs: extrRndx called on a non-exponent")
    indicatorBasis = S.fold mul M.empty numAvoid
indicator _ t = error ("Algebra.hs: indicator called on a non-base " ++ show t)

escapeSet :: Set Term -> Set Term -> Term -> Maybe (Set Term)
escapeSet ts a ct =
    if buildable ts a ct then
        Nothing
    else
        Just $ S.filter f ts
        where
          f (F (Enc _) [t, key]) =
              carriedBy ct t &&
              not (buildable ts a (inv key))
          f _ = False

isBase :: Term -> Bool
isBase (F Base _) = True
isBase _ = False

isExpr :: Term -> Bool
isExpr (G _) = True
isExpr _ = False

isVarExpr :: Term -> Bool
isVarExpr (G g) = isGroupVar g
isVarExpr _ = False

isRndx :: Term -> Bool
isRndx (G t) = isBasisVar t
isRndx _ = False

consts :: Term -> [Term]
consts (F Base _) = [F Base [F Genr []]]
consts (G _) = [G M.empty]
consts _ = []

-- Places

-- A place names a one subterm within a term.  It is a list of
-- integers giving a path through a term to that named subterm.  Each
-- integer in the list identifies the subterm in a function
-- application on the path to the named subterm.  The integer is the
-- index of the subterm in the application's list of terms.

newtype Place = Place [Int] deriving Show

-- Returns the places a variable occurs within a term.
places :: Term -> Term -> [Place]
places var source =
    f [] [] source
    where
      f paths path source
          | var == source = Place (reverse path) : paths
      f paths path (F _ u) =
          g paths path 0 u
      f paths path (G t) =      -- This case is broken
          groupPlaces (varId var) paths path 0 (linearize t)
      f paths _ _ = paths
      g paths _ _ [] = paths
      g paths path i (t : u) =
          g (f paths (i: path) t) path (i + 1) u

linearize :: Group -> [Id]
linearize t =
    do
      (x, (_, n)) <- M.assocs t
      replicate (if n >= 0 then n else negate n) x

-- This function is broken
--
groupPlaces ::  Id -> [Place] -> [Int] -> Int -> [Id] -> [Place]
groupPlaces x _ _ _ _ =
  error ("Algebra.groupPlaces failed for " ++ show x)

{-
groupPlaces _ paths _ _ [] = paths
groupPlaces x paths path i (y:ys) =
    let paths' = if x == y then
                     Place (reverse (i : path)) : paths
                 else paths in
    groupPlaces x paths' path (i + 1) ys
-}

-- Returns the places a term is carried by another term.
carriedPlaces :: Term -> Term -> [Place]
carriedPlaces target source =
    f [] [] source
    where
      f paths path source
          | target == source = Place (reverse path) : paths
      f paths path (F (Tupl _) ts) =
          foldl g paths (zip [0..] ts)
          where
            g paths (i, t) = f paths (i : path) t
      f paths path (F (Enc _) [t, _]) =
          f paths (0 : path) t
      f paths _ _ = paths

-- Returns the places a term is carried by another term.
carriedRelPlaces :: Term -> Term -> Set Term -> [Place]
carriedRelPlaces target source avoid =
    f [] [] source
    where
      f paths path source
          | relevant avoid source target = Place (reverse path) : paths
      f paths path (F (Tupl _) ts) =
          foldl g paths (zip [0..] ts)
          where
            g paths (i, t) = f paths (i : path) t
      f paths path (F (Enc _) [t, _]) =
          f paths (0 : path) t
      f paths _ _ = paths

-- Replace a variable within a term at a given place.
replace :: Term -> Place -> Term -> Term
replace var (Place ints) source =
    loop ints source
    where
      loop [] _ = var
      loop (i : path) (F s u) =
          F s (replaceNth (loop path (u !! i)) i u)
      loop _ _ = assertError "Algebra.replace: Bad path to term"

factors :: Group -> [(Id, (Sort, Int))]
factors t =
    do
      (x, (be, n)) <- M.assocs t
      case n >= 0 of
        True -> replicate n (x, (be, 1))
        False -> replicate (negate n) (x, (be, -1))

-- Return the ancestors of the term at the given place.
ancestors :: Term -> Place -> [Term]
ancestors source (Place ints) =
    loop [] ints source
    where
      loop ts [] _ = ts
      loop ts (i: path) t@(F _ u) =
          loop (t : ts) path (u !! i)
      loop ts [_] t@(G _) = t : ts
      loop _ _ _ = error "Algebra.ancestors: Bad path to term"

placeIsPrefixOf :: Place -> Place -> Bool
placeIsPrefixOf (Place l) (Place l') = L.isPrefixOf l l'

placeStripPrefix :: Place -> Place -> Maybe Place
placeStripPrefix (Place l) (Place l') =
  loop l l'
  where
    loop [] l' = Just $ Place l'
    loop (i : l) (i' : l') | i == i' = loop l l'
    loop _ _ = Nothing

-- Rename the identifiers in a term.  Gen keeps the state of the
-- renamer.  (Question: should alist be replaced by a Map?)
clone :: Gen -> Term -> (Gen, Term)
clone gen t =
    (gen', t')
    where
      (_, gen', t') = cloneTerm ([], gen) t
      cloneTerm (alist, gen) t =
          case t of             -- The association list maps
            I x ->              -- identifiers to identifier.
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
                        M.foldlWithKey cloneGroupList (alist, gen, []) t in
                (alist', gen', G $ group ts)
            D x ->              -- identifiers to identifier.
                case lookup x alist of
                  Just y -> (alist, gen, D y)
                  Nothing ->
                      let (gen', y) = cloneId gen x in
                      ((x, y) : alist, gen', D y)
            Z p -> (alist, gen, Z p)
            X x ->              -- identifiers to identifier.
                case lookup x alist of
                  Just y -> (alist, gen, X y)
                  Nothing ->
                      let (gen', y) = cloneId gen x in
                      ((x, y) : alist, gen', X y)
            Y p -> (alist, gen, Y p)
      cloneTermList (alist, gen, u) t =
          let (alist', gen', t') = cloneTerm (alist, gen) t in
          (alist', gen', t' : u)
      cloneGroupList (alist, gen, ts) x (be, n) =
          case lookup x alist of
            Just y -> (alist, gen, (y, (be, n)) : ts)
            Nothing ->
                let (gen', y) = cloneId gen x in
                ((x, y) : alist, gen', (y, (be, n)) : ts)

basePrecursor :: Gen -> Term -> (Gen, Term)
basePrecursor g (F Base [t]) =
  (g', F (Tupl "cat")
    [F Base [simplifyBase $ F Exp [t, G $ invert x']],
     G x'])
  where
    (g', x) = freshId g "w"
    G x' = groupVar Expt x
basePrecursor _ t =
  error ("Algebra.basePrecursor: Bad term " ++ show t)

simplifyBase :: Term -> Term
simplifyBase (F Exp [t, G g])
  | M.null g = simplifyBase t
simplifyBase (F Exp [F Exp [t, G g0], G g1]) =
  simplifyBase (F Exp [t, G (mul g0 g1)])
simplifyBase t = t

-- Functions used in both unification and matching

type IdMap = Map Id Term

emptyIdMap :: IdMap
emptyIdMap = M.empty

-- Apply a substitution to a term
idSubst :: IdMap -> Term -> Term
idSubst _ (F Exp []) = assertError "DiffieHellman.Algebra: Bad exponentiation"
idSubst subst (I x) =
    M.findWithDefault (I x) x subst
idSubst _ t@(C _) = t
idSubst subst (F (Invk op) [t]) =
    case idSubst subst t of
      F (Invk _) [t] -> t      -- Apply axiom
      t -> F (Invk op) [t]
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
idSubst subst (D x) =
    M.findWithDefault (D x) x subst
idSubst _ t@(Z _) = t
idSubst subst (X x) =
    M.findWithDefault (X x) x subst
idSubst _ t@(Y _) = t

-- Is every variable in a term a key in the map?
idMapped :: IdMap -> Term -> Bool
idMapped subst (I x) = M.member x subst
idMapped _ (C _) = True
idMapped subst (F _ u) =
    all (idMapped subst) u
idMapped subst (G t) =
    all (\ x -> M.member x subst) (M.keys t)
idMapped subst (D x) = M.member x subst
idMapped _ (Z _) = True
idMapped subst (X x) = M.member x subst
idMapped _ (Y _) = True

-- Unification and substitution

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

groupLookup :: IdMap -> Sort -> Id -> Group
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
-- (vars (h base) (x y rndx))
--
-- 1.  ((exp h x) y) ==> (exp h (mul x y))
-- 2.  (exp h (one)) ==> h
-- 3.  unify((exp(h, x)), (exp(h, y)), s) ==>
--         unify(x, y, s)
-- 4   unify((exp(h, x)), (exp((gen), y)), s) ==>
--         unify(h, (exp gen (mul y (rec x))), s)
-- 5.  unify((exp((gen), x)), (exp(h, y)), s) ==>
--         unify((exp(h, x)), (exp((gen), y)), s)

newtype Subst = Subst IdMap deriving (Eq, Ord)

instance Show Subst where
    showsPrec _ (Subst s) = showString "Subst (" . showMap s . showChar ')'

emptySubst :: Subst
emptySubst = Subst emptyIdMap

-- Is the domain of the substitution disjoint from
-- the variables in a list of terms?
disjointDom :: Subst -> [Term] -> Bool
disjointDom (Subst s) ts =
  all (allId $ flip S.notMember $ M.keysSet s) ts

allId :: (Id -> Bool) -> Term -> Bool
allId f (I x) = f x
allId _ (C _) = True
allId f (F _ u) = all (allId f) u
allId f (G g) = all f (M.keys g)
allId f (D x) = f x
allId _ (Z _) = True
allId f (X x) = f x
allId _ (Y _) = True

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
nonTrivialBinding x t@(G _) = not (t == groupVar Rndx x || t == groupVar Expt x)
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
chase (Subst s) (D x) =
    case M.lookup x s of
      Nothing -> D x
      Just t -> chase (Subst s) t
chase s (F (Invk op) [t]) = chaseInvk s op t
chase s (F Exp [t0, G t1]) = chaseExp s t0 t1
chase (Subst s) (G t) = G $ chaseGroup s t
chase _ t = t

chaseInvk :: Subst -> String -> Term -> Term
chaseInvk (Subst s) op (I x) =
    case M.lookup x s of
      Nothing -> F (Invk op) [I x]
      Just t -> chaseInvk (Subst s) op t
chaseInvk s _ (F (Invk _) [t]) = chase s t
chaseInvk _ op t = F (Invk op) [t]

chaseExp :: Subst -> Term -> Group -> Term
chaseExp s t0 t1
    | M.null t1 = chase s t0
chaseExp s@(Subst ss) (I x) t1 =
    case chase s (I x) of
      F Exp [t0', G t1'] ->
        chaseExpFinalize t0' t1t1'
        where t1t1' = mul t1' (chaseGroup ss t1)
      t0 -> chaseExpFinalize t0 t1'
        where t1' = chaseGroup ss t1
chaseExp s (F Exp [t0', G t1']) t1 =
    chaseExp s t0' (mul t1 t1')
chaseExp (Subst s) t0 t1 =
    chaseExpFinalize t0 t1'
    where t1' = chaseGroup s t1

chaseExpFinalize :: Term -> Group -> Term
chaseExpFinalize t0 t1 =
    if M.null t1
       then t0
       else F Exp [t0, G t1]

chaseGroup :: IdMap -> Group -> Group
chaseGroup s t =
    M.foldrWithKey f M.empty t
     where
       f x (be, c) t =
           mul (expg (chaseGroupLookup s be x) c) t

chaseGroupLookup :: IdMap -> Sort -> Id -> Group
chaseGroupLookup s be x =
    case M.lookup x s of
      Nothing -> groupVarG be x
      Just (G t) -> chaseGroup s t
      Just w -> error ("Algebra.chaseGroupLookup: Bad substitution: " ++
                     show x ++ " -> " ++ show w)

-- Does x occur in t?
occurs :: Id -> Term -> Bool
occurs x (I y) = x == y
occurs _ (C _) = False
occurs x (F _ u) = any (occurs x) u
occurs x (G t) = elem x (M.keys t)
occurs x (D y) = x == y
occurs _ (Z _) = False
occurs x (X y) = x == y
occurs _ (Y _) = False

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
unifyTerms (F (Invk "akey") [I x]) (F Pubk [I y]) s =
    unifyTerms (I x) (F (Invk "akey") [F Pubk [I y]]) s
unifyTerms (F (Invk "akey") [I x]) (F Pubk [C c, I y]) s =
    unifyTerms (I x) (F (Invk "akey") [F Pubk [C c, I y]]) s
unifyTerms (F Pubk [I x]) (F (Invk "akey") [I y]) s =
    unifyTerms (I y) (F (Invk "akey") [F Pubk [I x]]) s
unifyTerms (F Pubk [C c, I x]) (F (Invk "akey") [I y]) s =
    unifyTerms (I y) (F (Invk "akey") [F Pubk [C c, I x]]) s
unifyTerms (F Bltk u) (F Bltk u') s =
    L.nub $ unifyTermLists u u' s ++ unifyTermLists u (reverse u') s
unifyTerms (F Base [t0]) (F Base [t1]) s =
    unifyBase (chase (snd s) t0) (chase (snd s) t1) s
unifyTerms (F sym u) (F sym' u') s
    | sym == sym' = unifyTermLists u u' s
    | otherwise = []
unifyTerms (G t) (G t') s =
    unifyGroup t t' s
unifyTerms (D x) (D y) (g, Subst s)
    | x == y = [(g, Subst s)]
    | otherwise = [(g, Subst $ M.insert x (D y) s)]
unifyTerms (D x) (Z p) (g, Subst s) =
    [(g, Subst $ M.insert x (Z p) s)]
unifyTerms t (D x) s = unifyTerms (D x) t s
unifyTerms (Z p) (Z p') s
    | p == p' = [s]
    | otherwise = []
unifyTerms _ _ _ = []

-- unifyBase: the two terms were both encapsulated in F Base [].
-- feed the appropriate inputs to unifyExp.
-- Take h to mean h^1 for either base variable h or h = (gen).
-- Fall back to unify algorithm when left side is F Genr [].
unifyBase :: Term -> Term -> GenSubst -> [GenSubst]
unifyBase (F Exp [t0, G t1]) (F Exp [t0', G t1']) gs
  = unifyExp t0 t1 t0' t1' gs
unifyBase (F Exp [t0, G t1]) (I x) gs
  = unifyExp t0 t1 (I x) (M.empty) gs
unifyBase (F Exp [t0, G t1]) (F Genr []) gs
  = unifyExp t0 t1 (F Genr []) (M.empty) gs
unifyBase (I x) (F Exp [t0', G t1']) gs
  = unifyExp (I x) (M.empty) t0' t1' gs
unifyBase (I x) (I y) gs
  = unifyExp (I x) (M.empty) (I y) (M.empty) gs
unifyBase (I x) (F Genr []) gs
  = unifyExp (I x) (M.empty) (F Genr []) (M.empty) gs
unifyBase t0 t1 gs
  = unifyTerms t0 t1 gs

-- unifyExp: not guaranteed that inputs are not F Exp expressions.
-- guaranteed that t0 and t0' are (I x), (F Genr _), or (F Exp _).
-- Both t0 and t0' should not be F Exp, though, as this would indicate a non-canonical form.
unifyExp :: Term -> Group -> Term -> Group -> GenSubst -> [GenSubst]
unifyExp (F Exp t0) t1 _ _ _ =
  error ("Algebra.unifyExp: Got input not in canonical form " ++ show (F Exp t0) ++ show t1)
unifyExp _ _ (F Exp t0) t1 _ =
  error ("Algebra.unifyExp: Got input not in canonical form " ++ show (F Exp t0) ++ show t1)
-- Force into canonical form.
--unifyExp (F Exp [t0, G e]) t1 t0' t1' gs =
--  unifyExp t0 (mul e t1) t0' t1' gs
--unifyExp t0 t1 (F Exp [t0', G e]) t1' gs =
--  unifyExp t0 t1 t0' (mul e t1') gs
unifyExp t0 t1 t0' t1' s
    | t0 == t0' = unifyGroup t1 t1' s
unifyExp (I x1) t0 (I x2) t1' (g, Subst s) =
      unifyGroup (mul t0 z) t1' (g', Subst $ M.insert x1 (F Exp [(I x2), G z]) s)
      where
        (g', zid) = freshId g "z"
        z = groupVarGroup zid
unifyExp (I x) t1 (F Genr []) t1' (g, Subst s)
    | t1 == t1' =
        [(g, Subst $ M.insert x (F Genr []) s)]
    | otherwise =
        [(g, Subst (M.insert x (F Exp [F Genr [], G $ mul t1' (invert t1)]) s))]
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
      let t = groupSubst s (mul t0 (invert t1))
      (_, g', s') <- matchGroup t M.empty S.empty g s
      return (g', Subst s')

-- The exported unifier converts the internal representation of a
-- substitution into the external form using chaseMap.

unify :: Term -> Term -> GenSubst -> [GenSubst]
unify t t' (g, s) =
    do
      (g, s) <- unifyChase t t' (g, s)
      return (g, chaseMap s)

-- unify :: Term -> Term -> (Gen, Subst) -> [(Gen, Subst)]
-- unify t t' (g, s)
--   | badGen g t =
--       error ("unify: " ++ show g ++ ": " ++ show t)
--   | badGen g t' =
--       error ("unify: " ++ show g ++ ": " ++ show t')
--   | otherwise =
--       maybe [] (\s -> [(g, s)]) $ unifyI t t' s

-- Apply the chasing version of substitution to the range of s.

chaseMap :: Subst -> Subst
chaseMap (Subst s) =
    Subst $ M.map (substChase (Subst s)) s

-- A chasing version of substitution.

substChase :: Subst -> Term -> Term
substChase subst@(Subst ss) t =
    case chase subst t of
      t@(I _) -> t
      t@(C _) -> t
      F (Invk op) [t] ->
          case substChase subst t of
            F (Invk op') [t] | op == op' -> t -- Apply axiom
            t -> F (Invk op) [t]
      F Exp [t0, G t1] ->
          case substChase subst t0 of
            F Exp [t0', G t1'] ->
              case mul t1' $ chaseGroup ss t1 of
                t2 | M.null t2 -> t0'
                   | otherwise -> F Exp [t0', G t2]
            t -> chaseExp subst t t1
      F s u ->
          F s (map (substChase subst) u)
      G t -> G $ chaseGroup ss t
      t@(D _) -> t
      t@(Z _) -> t
      t@(X _) -> t
      t@(Y _) -> t

destroyer :: Term -> Maybe Subst
destroyer t@(G m) | isVar t =
  Just $ Subst (M.fromList [(head $ M.keys m, G M.empty)])
destroyer _ = Nothing

-- Extend a substitution so that it satisfies an absence assertion
absentSubst :: (Gen, Subst) -> (Term, Term) -> [(Gen, Subst)]
absentSubst gs (G v, G t) | isGroupVar v =
  case separateVar (getGroupVar v) t of
    Nothing -> [gs]
    Just (v', t') -> unifyGroup v' t' gs
absentSubst _ ts =
  error ("Algebra.absentSubst: Bad absent pair " ++ show ts)

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

-- Is every variable in t in the domain of r?
matched :: Env -> Term -> Bool
matched (Env (_, r)) t = idMapped r t

-- Apply a substitution to the range of an environment
substUpdate :: Env -> Subst -> Env
substUpdate (Env (x, r)) s =
  Env (x, M.map (substitute s) r)

-- The matcher has the property that when pattern P and term T match
-- then instantiate (match P T emptyEnv) P = T.

-- Important discipline to maintain during match:
-- Terms are either "source" or "destination / flex" terms, and these two
-- categories should be kept strictly separate.
--   the first parameter is a source term.
--   the second parameter is a destination/flex term.
--   v is a set of destination/flex IDs.
--   g is a generator for the destination/flex algebra
--   variables in the domain of r are source variables
--   terms in the range of r are destination/flex terms.

type GenEnv = (Gen, Env)

match ::  Term -> Term -> GenEnv -> [GenEnv]
match (I x) t (g, Env (v, r)) =
  case M.lookup x r of
    Nothing -> [(g, Env (v, M.insert x t r))]
    Just t' -> if t == t' then [(g, Env (v, r))] else []
match (C c) (C c') ge = if c == c' then [ge] else []
match (F Base [t0]) (F Base [t1]) ge =
  matchBase t0 t1 ge
match (F Bltk u) (F Bltk u') ge =
  L.nub $ matchLists u u' ge ++ matchLists u (reverse u') ge
match (F s u) (F s' u') ge
  | s == s' = matchLists u u' ge
match (F (Invk op) [t]) t' ge =
  match t (F (Invk op) [t']) ge
match (G t) (G t') (g, Env (v, r)) =
  do
    (v', g', r') <- matchGroup t t' v g r
    return (g', Env(v', r'))
match (D x) t (g, Env (v, r)) =
  case M.lookup x r of
    Nothing -> [(g, Env (v, M.insert x t r))]
    Just t' -> if t == t' then [(g, Env (v, r))] else []
match (Z p) (Z p') r = if p == p' then [r] else []
match (X x) t (g, Env (v, r)) =
  case M.lookup x r of
    Nothing -> [(g, Env (v, M.insert x t r))]
    Just t' -> if t == t' then [(g, Env (v, r))] else []
match (Y p) (Y p') r = if p == p' then [r] else []
match _ _ _ = []

-- On input t, outputs (b, e) such that if t is of sort base then
-- t = b^e and b is a variable or (gen).
-- If t is not of sort base, outputs (t, 1).
calcBase :: Term -> (Term, Group)
calcBase (I x) = ((I x), M.empty)
calcBase (F Genr _) = (F Genr [], M.empty)
calcBase (F Exp [(I x), G e]) = ((I x), e)
calcBase (F Exp [F Genr _, G e]) = (F Genr [], e)
calcBase (F Exp [F Exp [b, G e1], G e2]) = calcBase (F Exp [b, G $ mul e1 e2])
-- Well-formed versions.  Is this necessary?
calcBase (F Base [I x]) = (F Base [I x], M.empty)
calcBase (F Base [F Genr _]) = (F Base [F Genr []], M.empty)
calcBase (F Base [F Exp [(I x), G e]]) = (F Base [I x], e)
calcBase (F Base [F Exp [F Genr _, G e]]) = (F Base [F Genr []], e)
calcBase (F Base [F Exp [F Exp [b, G e1], G e2]]) = calcBase (F Base [F Exp [b, G $ mul e1 e2]])
calcBase t = (t, M.empty)

-- matchBase: the two terms were both encapsulated in F Base [].
-- feed the appropriate inputs to matchExp.
-- Take h to mean h^1 for either base variable h or h = (gen).
-- Fall back to match algorithm when left side is F Genr [].

matchBase :: Term -> Term -> GenEnv -> [GenEnv]
-- matchBase x y (g, _)
--   | badGen g (F Base [x]) =
--     error ("matchBase: " ++ show g ++ ": " ++ show x)
--   | badGen g (F Base [y]) =
--     error ("matchBase: " ++ show g ++ ": " ++ show y)
matchBase (F Exp [t0, G t1]) (F Exp [t0', G t1']) ge
  = matchExp t0 t1 t0' t1' ge
matchBase (F Exp [t0, G t1]) (I x) ge
  = matchExp t0 t1 (I x) (M.empty) ge
matchBase (F Exp [t0, G t1]) (F Genr []) ge
  = matchExp t0 t1 (F Genr []) (M.empty) ge
matchBase (I x) (F Exp [t0', G t1']) ge
  = matchExp (I x) (M.empty) t0' t1' ge
matchBase (I x) (I y) ge
  = matchExp (I x) (M.empty) (I y) (M.empty) ge
matchBase (I x) (F Genr []) ge
  = matchExp (I x) (M.empty) (F Genr []) (M.empty) ge
matchBase t0 t1 ge
  = match t0 t1 ge

{-
  case M.lookup x r of
    Nothing -> match (I x) (F Exp [b,e]) (g, Env (v,r))
    Just (F Exp [b',e']) -> if (bb == bb') then
                match (G M.empty) (G (mul ee (invert ee'))) (g, Env (v, r)) else []
                where
                  (bb', ee') = calcBase (F Exp [b',e'])
    Just (I y) -> if ((I y) == bb) then
                    match (G M.empty) (G ee) (g, Env (v, r)) else []
    Just _ -> []
  where
    (bb, ee) = calcBase t1
match (F Base [I x]) (F Base [I y]) (g, Env (v, r)) =
  case M.lookup x r of
    Nothing -> match (I x) (I y) (g, Env (v,r))
    Just (F Exp [b',e']) -> if (bb' == (I y)) then
                match (G M.empty) (G ee') (g, Env (v,r)) else []
                where
                  (bb', ee') = calcBase (F Exp [b',e'])
    Just _ -> match (I x) (I y) (g, Env (v, r))
-}

-- matchExp: not guaranteed that inputs are not F Exp expressions.
-- guaranteed that t0 is either an I x or an F Exp [] term.
-- guaranteed that t0' is I x, F Genr, or F Exp.
-- in match t0 t1 t0' t1' ge: t0 and t1 are source material, t0', t1' are destination/flex material.
-- Both t0 and t0' should not be F Exp, though, as this would indicate a non-canonical form.
matchExp ::  Term -> Group -> Term -> Group -> GenEnv -> [GenEnv]
matchExp (F Exp [t0, G e]) t1 _ _ _ =
    error ("Algebra.matchExp: Input not in canonical form " ++ show (F Exp [F Exp [t0, G e], G t1]))
matchExp _ _ (F Exp [t0, G e]) t1 _ =
    error ("Algebra.matchExp: Input not in canonical form " ++ show (F Exp [F Exp [t0, G e], G t1]))
-- Force both inputs into canonical form
--matchExp (F Exp [t0, G e]) t1 t0' t1' ge =
--    matchExp t0 (mul e t1) t0' t1' ge
--matchExp t0 t1 (F Exp [t0', G e]) t1' ge =
--    matchExp t0 t1 t0' (mul e t1') ge
matchExp (I x) t1 t0' t1' ge@(g, Env (v, r)) =
    case M.lookup x r of
      -- if x is already mapped, it needs to be mapped to a power of the base of t0'
      Just t  -- t is destination/flex material
          | fst (calcBase t0') == fst (calcBase t) ->
            match (G t1) (G (mul t1' (mul (snd $ calcBase t0') (invert (snd $ calcBase t))))) ge
          | otherwise -> []
      _ -> matchLists [I x, G t1] [F Exp [t0', G w], G (mul t1' (invert w))]
           (g', Env (S.insert wid v, r))
      where
        (g', wid) = freshId g "w"
        w = groupVarGroup wid
matchExp (F Genr []) t1 t0' t1' ge =
    matchLists [F Genr [], G t1] [t0', G t1'] ge
matchExp t e t' e' _ = error ("Algebra.matchExp: Bad match term" ++ show t ++ show e ++ show t' ++ show e')

-- in matchLists u u' ge: u is a list of source terms and u' is a list of destination/flex terms.
matchLists :: [Term] -> [Term] -> GenEnv -> [GenEnv]
matchLists [] [] ge = [ge]
matchLists (t : u) (t' : u') ge =
  do
    ge' <- match t t' ge
    matchLists u u' ge'
matchLists _ _ _ = []

-- Matching in a group

-- t0 is the pattern
-- t1 is the target term
-- v is the set of previously freshly generated variables
-- g is the generator

-- Returns complete set of unifiers.  Each unifier includes the set of
-- variables freshly generated and a generator.

matchGroup ::  Group -> Group -> Set Id -> Gen ->
               IdMap -> [(Set Id, Gen, IdMap)]
matchGroup t0 t1 v g r =
  let (t0', t1') = merge t0 t1 r       -- Apply subst to LHS
      (v', g', r') = genVars v g t0' r -- Gen vars for non-fresh vars
      d = mkInitMatchDecis v' t1' in -- Ensure rndxs on RHS stay distinct
  case partition (groupSubst r' t0') t1' v' of
    ([], []) -> return (v', g', r')
    ([], t) -> constSolve t v' g' r' d -- No variables of sort expr here
    (t0, t1) -> solve t0 t1 v' g' r' d

-- Apply subst to LHS and add results to RHS
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
                error $ "Algebra.merge: expecting an rndx but got " ++ show t

-- Generate vars for each non-fleshly generated vars
genVars :: Set Id -> Gen -> Group -> IdMap -> (Set Id, Gen, IdMap)
genVars v g t r =
  M.foldlWithKey genVar (v, g, r) t
  where
    genVar (v, g, r) x (be, _)
      | S.member x v = (v, g, r)
      | otherwise =
        (S.insert x' v, g', M.insert x (groupVar be x') r)
        where
          (g', x') = cloneId g x

-- This was the long used version, but it generates fresh vars fo all
-- vars in t.
{-
genVars :: Set Id -> Gen -> Group -> IdMap -> (Set Id, Gen, IdMap)
genVars v g t r =
  M.foldlWithKey genVar (v, g, r) t
  where
    genVar (v, g, r) x (be, _) =
      (S.insert x' v, g', M.insert x (groupVar be x') r)
      where
        (g', x') = cloneId g x
--}

-- A set of decisions records rndx variables that have been identified
-- and those that are distinct.
data Decision t = Decision
  { same :: [(t, t)],
    dist :: [(t, t)] }
  deriving Show

-- Create an initial set of decisions
mkDecis :: Decision Id
mkDecis =
  Decision {
    same = [],
    dist = [] }

-- Ensure non-freshly generated bases elements in t are never identified
mkInitMatchDecis :: Set Id -> Group -> Decision Id
mkInitMatchDecis vs t =
  mkDecis { dist = [(x, y) | x <- v, y <- v, x /= y] }
  where
    v = [x | (x, (be, _)) <- M.assocs t, be == Rndx, not $ S.member x vs]

-- Move fresh variables on the RHS of the equation to the LHS
-- Move variables of sort rndx on the LHS to the RHS
partition ::  Group -> Group -> Set Id -> ([Maplet], [Maplet])
partition t0 t1 v =
  (M.assocs lhs, M.assocs rhs)
  where
    (v1, c1) = M.partitionWithKey g t1 -- Fresh variables go in v1
    g x y = S.member x v && f y        -- only when they are exprs
    (v0, c0) = M.partition f t0        -- Basis elements go in c0
    f (be, _) = be /= Rndx
    lhs = mul v0 (invert v1)
    rhs = mul c1 (invert c0)

-- Solve equation when there are no variables of sort expr on LHS.
-- Treat all variables as constants.
constSolve :: [Maplet] -> Set Id -> Gen -> IdMap ->
              Decision Id -> [(Set Id, Gen, IdMap)]
constSolve t v g r d
  | any (\(_, (be, _)) -> be /= Rndx) t = [] -- Fail expr var is on RHS
  | otherwise = constSolve1 t v g r d    -- All vars are rndx

constSolve1 :: [Maplet] -> Set Id -> Gen ->
               IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
constSolve1 [] v g r _ = return (v, g, r)
constSolve1 t v g r d =
  case orientDecis v $ nextDecis d t of
    [] -> []                    -- All decisions already made
    ((x, y):_) ->               -- Pick first undecided pair
      distinct ++ identified
      where
        distinct = constSolve1 t v g r neq
        neq = d {dist = (x, y):(y, x):dist d} -- Add new constraints
        -- eliminate x
        identified = constSolve1 t' v' g r' d'
        t' = identify x y t     -- Equate x y in t
        v' = S.delete x v       -- Eliminate x in v
        r' = eliminate x y' r   -- And in r
        y' = groupVar Rndx y
        d' = d {same = (x, y):same d} -- And note decision

-- Find a pair of variables for which no decision has been made.
nextDecis :: Decision Id -> [Maplet] -> [(Id, Id)]
nextDecis d t =
  [(x, y) | x <- vars, y <- vars, x < y,
    not $ decided d x y]
  where
    vars = foldr f [] t
    f (x, (Rndx, _)) v = x:v
    f (_, (Expt, _)) v = v
    decided d x y =             -- Is x and y decided?
      u == v ||
      any f (dist d)
      where
        u = chase x       -- Find canonical representitive for x and y
        v = chase y
        f (w, z) = chase w == u && chase z == v
        chase = listChase (same d)

-- Find canonical representive of the set of identified variables.
listChase :: Eq t => [(t, t)] -> t -> t
listChase d x =
  case lookup x d of
    Nothing -> x
    Just y -> listChase d y

-- Ensure first var in pair is in v.
orientDecis :: Set Id -> [(Id, Id)] -> [(Id, Id)]
orientDecis v undecided =
  map f undecided
  where
    f (x, y)
      | S.notMember x v = (y, x)
      | otherwise = (x, y)

-- Modify t by replacing x by y.
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

-- Solve when variables of sort expr are on LHS.  This involves
-- solving using the group axioms.  The algorithm for matching in the
-- group without added constant symbols is the same as the one for
-- unification with constant symbols.
--
-- For this description, additive notation is used for the group.  To
-- show sums, we write
--
--     sum[i] c[i]*x[i] for c[0]*x[0] + c[1]*x[1] + ... + c[n-1]*x[n-1].
--
-- The unification problem is to solve
--
--     sum[i] c[i]*x[i] = sum[j] d[j]*y[j]
--
-- where x[i] is a variable and y[j] is a constant symbol.
--
-- The algorithm used to find solutions is described in Vol. 2 of The
-- Art of Computer Programming / Seminumerical Alorithms, 2nd Ed.,
-- 1981, by Donald E. Knuth, pg. 327.
--
-- The algorithm's initial values are the linear equation (c,d) and an
-- empty substitution s.
--
-- 1.  Let c[i] be the smallest non-zero coefficient in absolute value.
--
-- 2.  If c[i] < 0, multiply c and d by -1 and goto step 1.
--
-- 3.  If c[i] = 1, a general solution of the following form has been
-- found:
--
--       x[i] = sum[j] -c'[j]*x[j] + d[k] for all k
--
--  where c' is c with c'[i] = 0.  Use the equation to eliminate x[i]
--  from the range of the current substitution s.  If variable x[i] is
--  in the original equation, add the mapping to substitution s.
--
-- 4.  If c[i] divides every coefficient in c,
--
--     * if c[i] divides every constant in d, divide c and d by c[i]
--       and goto step 3,
--
--     * otherwise fail because there is no solution.  In this case
--       rndx vars must be identified.
--
-- 5.  Otherwise, eliminate x[i] as above in favor of freshly created
-- variable x[n], where n is the length of c.
--
--      x[n] = sum[j] (c[j] div c[i] * x[j])
--
-- Goto step 1 and solve the equation:
--
--      c[i]*x[n] + sum[j] (c[j] mod c[i])*x[j] = d[k] for all k

solve ::  [Maplet] -> [Maplet] -> Set Id -> Gen ->
          IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
solve t0 t1 v g r d =
  let (x, ci, i) = smallest t0 in -- ci is the smallest coefficient,
  case compare ci 0 of            -- x is its variable, i its position
    GT -> agSolve x ci i t0 t1 v g r d
    LT -> agSolve x (-ci) i (mInverse t0) (mInverse t1) v g r d -- Step 2
    EQ -> assertError "Algebra.solve: zero coefficient found"

-- Find the factor with smallest coefficient in absolute value.
-- Returns the variable, the coefficient, and the position within the
-- list.
smallest :: [Maplet] -> (Id, Int, Int)
smallest [] = assertError "Algebra.smallest given an empty list"
smallest t =
  loop (Id (0, "x")) 0 0 0 0 t
  where
    loop v ci i _ _ [] = (v, ci, i)
    loop v ci i a j ((x, (_, c)):t) =
      if a < abs c then
        loop x c j (abs c) (j + 1) t
      else
        loop v ci i a (j + 1) t

-- The group axioms are abbreviated by AG.
agSolve :: Id -> Int -> Int -> [Maplet] -> [Maplet] -> Set Id -> Gen ->
          IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
agSolve x 1 i t0 t1 v g r _ =    -- Solve for x and return answer
  return (S.delete x v, g, eliminate x t r) -- Step 3
  where
    t = G $ group (t1 ++ (mInverse (omit i t0)))
agSolve x ci i t0 t1 v g r d
  | divisible ci t0 =           -- Step 4
    if divisible ci t1 then     -- Solution found
      agSolve x 1 i (divide ci t0) (divide ci t1) v g r d
    else         -- No possible solution without identifying variables
      identSolve x ci i t0 t1 v g r d
  | otherwise =                 -- Step 5, eliminate x in favor of x'
      solve t0' t1 (S.insert x' $ S.delete x v) g' r' d
      where
        (g', x') = cloneId g x
        t = G $ group ((x', (Expt, 1)) :
                       mInverse (divide ci (omit i t0)))
        r' = eliminate x t r
        t0' = (x', (Expt, ci)) : modulo ci (omit i t0)

eliminate :: Id -> Term -> IdMap -> IdMap
eliminate x t r =
  M.map (idSubst (M.singleton x t)) r

omit :: Int -> [a] -> [a]
omit 0 (_:l) = l
omit n _ | n < 0 = assertError "Algebra.omit: negative number given to omit"
omit n (_:l) = omit (n - 1) l
omit _ [] = assertError "Algebra.omit: number given to omit too large"

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

-- Explore two choices as to whether to identify a pair of variables.
identSolve :: Id -> Int -> Int -> [Maplet] -> [Maplet] -> Set Id -> Gen ->
              IdMap -> Decision Id -> [(Set Id, Gen, IdMap)]
identSolve z ci i t0 t1 v g r d =
  case orientDecis v $ nextDecis d t1 of
    [] -> []
    ((x, y):_) ->
      distinct ++ identified
      where
        distinct = identSolve z ci i t0 t1 v g r neq
        neq = d {dist = (x, y):(y, x):dist d}
        -- eliminate x
        identified = agSolve z ci i t0 t1' v' g r' d'
        t1' = identify x y t1   -- Equate x y in t1
        v' = S.delete x v       -- Eliminate x in v
        r' = eliminate x y' r   -- And in r
        y' = groupVar Rndx y
        d' = d {same = (x, y):same d}

-- Cast an environment into a substitution by filtering out trivial
-- bindings.

substitution :: Env -> Subst
substitution (Env (_, r)) =
    Subst $ M.filterWithKey nonTrivialBinding r

-- Find bound above all the strand indices i in strand values Z i in
-- values in the environment
strandBoundEnv :: Env -> Int
strandBoundEnv (Env (_, map)) =
    M.foldl f 0 map
     where
       f bnd (Z i) = max bnd (i+1)
       f bnd _ = bnd

-- Add type information to an environment, and return it as a list of
-- associations.

reify :: [Term] -> Env -> [(Term, Term)]
reify domain (Env (_, env)) =
    map (loop domain) $ M.assocs env
    where
      loop [] (x, _) =
          error $ "Algebra.reify: variable missing from domain " ++ idName x
      loop (I x : _) (y, t)
          | x == y = (I x, t)
      loop (F op@(Data _) [I x] : _) (y, t)
          | x == y = (F op [I x], F op [t])
      loop (F op@(Akey _) [I x] : _) (y, t)
          | x == y = (F op [I x], F op [t])
      loop (F Name [I x] : _) (y, t)
          | x == y = (F Name [I x], F Name [t])
      loop (F Pval [I x] : _) (y, t)
          | x == y = (F Pval [I x], F Pval [t])
      loop (F Chan [I x] : _) (y, t)
          | x == y = (F Chan [I x], F Chan [t])
      loop (F Locn [I x] : _) (y, t)
          | x == y = (F Locn [I x], F Locn [t])
      loop (F Base [I x] : _) (y, t)
          | x == y = (F Base [I x], F Base [t])
      loop (G x : _) (y, G t)
          | isGroupVar x && varId (G x) == y = (G x, G t)
      loop (D x : _) (y, t)
          | x == y = (D x, t)
      loop (X x : _) (y, t)
          | x == y = (X x, t)
      loop (_ : domain) pair = loop domain pair

strdMatch ::  Term -> Int -> GenEnv -> [GenEnv]
strdMatch t p env = match t (Z p) env

strdLookup :: Env -> Term -> Maybe Int
strdLookup env t =
  case instantiate env t of
    Z p -> Just p
    _ -> Nothing

strdUpdate :: Env -> (Int -> Int) -> Env
strdUpdate (Env (g, e)) f =
  Env (g, M.map h e)
  where
    h (Z z) = Z $ f z
    h t = t

--   indxMatch ::  Term -> Int -> (Gen, Env) -> [(Gen, Env)]
--   indxMatch t t' (g, e) =
--          maybe [] (\e -> [(g, e)]) $ indxMatchI t t' e
--
--   indxMatchI ::  Term -> Int -> Env -> Maybe Env
--   indxMatchI t p env = matchI t (Y p) env

indxLookup :: Env -> Term -> Maybe Int
indxLookup env t =
  case instantiate env t of
    Y p -> Just p
    _ -> Nothing

indxUpdate :: Env -> (Int -> Int) -> Env
indxUpdate (Env (g, e)) f =
  Env (g, M.map h e)
  where
    h (Y z) = Y $ f z
    h t = t

indxOfInt :: Int -> Term
indxOfInt i = Y i

-- Term specific loading functions

loadVars :: MonadFail m => Sig -> Gen -> [SExpr Pos] -> m (Gen, [Term])
loadVars sig gen sexprs =
    do
      pairs <- mapM loadVarPair sexprs
      (g, vars) <- foldM (loadVar sig) (gen, []) (concat pairs)
      return (g, reverse vars)

loadVarPair :: MonadFail m => SExpr Pos -> m [(SExpr Pos, SExpr Pos)]
loadVarPair (L _ (x:y:xs)) =
    let (t:vs) = reverse (x:y:xs) in
    return [(v,t) | v <- reverse vs]
loadVarPair x = fail (shows (annotation x) "Malformed vars declaration")

loadVar :: MonadFail m => Sig -> (Gen, [Term]) -> (SExpr Pos, SExpr Pos) ->
           m (Gen, [Term])
loadVar sig (gen, vars) (S pos name, S pos' sort) =
    case loadLookup pos vars name of
      Right _ ->
          fail (shows pos "Duplicate variable declaration for " ++ name)
      Left _ ->
          do
            let (gen', x) = freshId gen name
            p <- mkVar sig pos' sort x
            return (gen', p : vars)
loadVar _ _ (x,_) = fail (shows (annotation x) "Bad variable syntax")

mkVar :: MonadFail m => Sig -> Pos -> String -> Id -> m Term
mkVar sig pos sort x
  | sort == "name" = return $ F Name [I x]
  | sort == "pval" = return $ F Pval [I x]
  | sort == "chan" = return $ F Chan [I x]
  | sort == "locn" = return $ F Locn [I x]
  | sort == "base" = return $ F Base [I x]
  | sort == "expt" = return $ groupVar Expt x
  | sort == "rndx" = return $ groupVar Rndx x
  | sort == "mesg" = return $ I x
  | sort == "strd" = return $ D x
  | sort == "indx" = return $ X x
  | elem sort (Sig.akeys sig) = return $ F (Akey sort) [I x]
  | elem sort (Sig.atoms sig) = return $ F (Data sort) [I x]
  | otherwise = fail (shows pos "Sort " ++ sort ++ " not recognized")

newVar :: Sig -> Gen -> String -> String -> (Gen, Term)
newVar sig g varName varSort =
    let (g', x) = freshId g varName in
    (g', mkVarUnfailingly sig varSort x)

newVarDefault :: Gen -> String -> String -> (Gen, Term)
newVarDefault = newVar Sig.defaultSig
    

mkVarUnfailingly :: Sig -> String -> Id -> Term
mkVarUnfailingly sig sort x
  | sort == "name" = F Name [I x]
  | sort == "pval" = F Pval [I x]
  | sort == "chan" = F Chan [I x]
  | sort == "locn" = F Locn [I x]
  | sort == "mesg" = I x
  | sort == "strd" = D x
  | sort == "indx" = X x
  | elem sort (Sig.akeys sig) = F (Akey sort) [I x]
  | elem sort (Sig.atoms sig) = F (Data sort) [I x]
  | otherwise =  I x    -- Default:  Var of sort mesg

varName :: Term -> String
varName t = idName (varId t)

loadLookup :: Pos -> [Term] -> String -> Either String Term
loadLookup pos [] name = Left (shows pos $ "Identifier " ++ name ++ " unknown")
loadLookup pos (t : u) name =
    let name' = idName (varId t) in
    if name' == name then Right t else loadLookup pos u name

loadLookupStrict :: Pos -> [Term] -> String -> Either String Term
loadLookupStrict pos vars name =
  case loadLookup pos vars name of
    Left msg -> Left msg
    Right t | not (isExpr t) || isRndx t -> Right t
    _ -> Left (shows pos $ "Identifier " ++ name ++
               " is an expt--must be a rndx")

loadLookupName :: MonadFail m => Pos -> [Term] -> String -> m Term
loadLookupName pos vars name =
    either fail f (loadLookup pos vars name)
    where
      f t@(F Name [I _]) = return t
      f _ = fail (shows pos $ "Expecting " ++ name ++ " to be a name")

loadLookupAkey :: MonadFail m => Pos -> [Term] -> String ->
                  m (String, Term)
loadLookupAkey pos vars name =
    either fail f (loadLookup pos vars name)
    where
      f t@(F (Akey op) [I _]) = return (op, t)
      f _ = fail (shows pos $ "Expecting " ++ name ++ " to be an akey")

-- Load term and check that it is well-formed.
-- Load in strict mode when the third argument is true.
-- In this case, make sure that when an exponent is a carried term,
-- the exponent is a rndx variable reference.
loadTerm :: MonadFail m => Sig -> [Term] -> Bool -> SExpr Pos -> m Term
loadTerm _ vars True (S pos s) =
    either fail return (loadLookupStrict pos vars s)
loadTerm _ vars False (S pos s) =
    either fail return (loadLookup pos vars s)
loadTerm _ _ _ (Q _ t) =
    return (C t)
loadTerm sig vars strict (L pos (S _ s : l)) =
    case lookup s loadDispatch of
      Nothing ->
        case Sig.findOper s (Sig.opers sig) of
          Nothing -> fail (shows pos "Keyword " ++ s ++ " unknown")
          Just op -> loadOper sig pos vars strict op l
      Just f -> f sig pos vars strict l
loadTerm _ _ _ x = fail (shows (annotation x) "Malformed term")

type LoadFunction m = Sig -> Pos -> [Term] -> Bool -> [SExpr Pos] -> m Term

loadDispatch :: MonadFail m => [(String, LoadFunction m)]
loadDispatch =
    [("pubk", loadPubk)
    ,("privk", loadPrivk)
    ,("invk", loadInvk)
    ,("ltk", loadLtk)
    ,("bltk", loadBltk)
    ,("gen", loadGen)
    ,("exp", loadExp)
    ,("one", loadOne)
    ,("rec", loadRec)
    ,("mul", loadMul)
    ,("cat", loadCat)
    ]

locnMesg :: Term -> Term -> Term
locnMesg pt t =
    F (Tupl "cat") [pt, t]

isLocnMsg :: Term -> Bool
isLocnMsg (F (Tupl "cat") [pt, _]) =
    case pt of
      F Pval [I _] -> True
      _ ->  False
isLocnMsg _ = False

locnMsgPayload :: Term -> Term
locnMsgPayload m@(F (Tupl "cat") [pt, t]) =
    case pt of
      F Pval [I _] -> t
      _            -> m
locnMsgPayload x = x

locnMsgPoint :: MonadFail m => Term -> m Term
locnMsgPoint (F (Tupl "cat") [pt, _]) =
    case pt of
      F Pval [I _] -> return pt
      _ -> fail ("locnMsgPoint:  Bad point " ++ show pt)
locnMsgPoint x =
    fail ("locnMsgPoint:  Bad state message " ++ show x)

loadLocnTerm :: MonadFail m => Sig -> Gen -> SExpr Pos ->
                SExpr Pos -> Term -> m (Gen, Term, Term)
loadLocnTerm sig gen (S pos ptStr) (S pos' pvalStr) t =
    do
      (gen', vars) <- loadVar sig (gen, []) (S pos ptStr, S pos' pvalStr)
      case vars of
        []     -> fail (shows pos "No variable generated by loadVar in loadLocnTerm")
        pt : _ -> return (gen', pt, locnMesg pt t)
loadLocnTerm _ _ _ _ _ =
    fail "loadLocnTerm:  Call only with SExprs that are really Strings"

-- Atom constructors: pubk privk invk ltk

loadPubk :: MonadFail m => LoadFunction m
loadPubk _ _ vars _ [S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [I $ varId t]]
loadPubk _ _ vars _ [Q _ c, S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [C c, I $ varId t]]
loadPubk _ pos _ _ _ = fail (shows pos "Malformed pubk")

loadPrivk :: MonadFail m => LoadFunction m
loadPrivk _ _ vars _ [S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [I $ varId t]]]
loadPrivk _ _ vars _ [Q _ c, S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [C c, I $ varId t]]]
loadPrivk _ pos _ _ _ = fail (shows pos "Malformed privk")

loadInvk :: MonadFail m => LoadFunction m
loadInvk _ _ vars _ [S pos s] =
    do
      (op, t) <- loadLookupAkey pos vars s
      return $ F (Akey op) [F (Invk op) [I $ varId t]]
loadInvk _ _ vars _ [L _ [S _ pubk, S pos s]]
  | pubk == "pubk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [I $ varId t]]]
loadInvk _ _ vars _ [L _ [S _ pubk, Q _ c, S pos s]]
  | pubk == "pubk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [C c, I $ varId t]]]
loadInvk _ _ vars _ [L _ [S _ privk, S pos s]]
  | privk == "privk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [I $ varId t]]
loadInvk _ _ vars _ [L _ [S _ privk, Q _ c, S pos s]]
  | privk == "privk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [C c, I $ varId t]]
loadInvk sig _ vars strict [L _ [S _ invk, t]]
  | invk == "invk" =
    do
      a <- loadTerm sig vars strict t
      case a of
        F (Akey _) _ -> return a
        _ -> fail (shows (annotation t) "Expecting an akey")
loadInvk _ pos _ _ _ = fail (shows pos "Malformed invk")

loadLtk :: MonadFail m => LoadFunction m
loadLtk _ _ vars _ [S pos s, S pos' s'] =
    do
      t <- loadLookupName pos vars s
      t' <- loadLookupName pos' vars s'
      return $ F (Data "skey") [F Ltk [I $ varId t, I $ varId t']]
loadLtk _ pos _ _ _ = fail (shows pos "Malformed ltk")

loadBltk :: MonadFail m => LoadFunction m
loadBltk _ _ vars _ [S pos s, S pos' s'] =
    do
      t <- loadLookupName pos vars s
      t' <- loadLookupName pos' vars s'
      return $ F (Data "skey") [F Bltk [I $ varId t, I $ varId t']]
loadBltk pos _ _ _ _ = fail (shows pos "Malformed bltk")

-- Base and exponents

loadGen :: MonadFail m => LoadFunction m
loadGen _ _ _ _ [] =
    return $ F Base [F Genr []]
loadGen _ pos _ _ _ = fail (shows pos "Malformed gen")

loadExp :: MonadFail m => LoadFunction m
loadExp sig _ vars _ [x, x'] =
    do
      t <- loadBase sig vars x
      t' <- loadExpr sig vars False x'
      return $ F Base [idSubst emptyIdMap $ F Exp [t, G t']]
loadExp _ pos _ _ _ = fail (shows pos "Malformed exp")

loadBase :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadBase sig vars x =
    do
      t <- loadTerm sig vars False x
      case t of
        F Base [t] -> return t
        _ -> fail (shows (annotation x) "Malformed base")

loadExpr :: MonadFail m => Sig -> [Term] -> Bool -> SExpr Pos -> m Group
loadExpr sig vars False x =
    do
      t <- loadTerm sig vars False x
      case t of
        G t -> return t
        _ -> fail (shows (annotation x) "Malformed expr")
loadExpr sig vars True x = loadExpr sig vars False x
--loadExpr _ True x =
--    do
--      fail (shows (annotation x) "Disallowed bare exponent")

loadOne :: MonadFail m => LoadFunction m
loadOne _ _ _ False [] =
    return $ G M.empty
loadOne _ pos _ True _ = fail (shows pos "Disallowed bare exponent")
loadOne _ pos _ _ _ = fail (shows pos "Malformed one")

loadRec :: MonadFail m => LoadFunction m
loadRec sig _ vars False [x] =
    do
      t <- loadExpr sig vars False x
      return $ G $ invert t
loadRec _ pos _ True _ = fail (shows pos "Disallowed bare exponent")
loadRec _ pos _ _ _ = fail (shows pos "Malformed rec")

loadMul :: MonadFail m => LoadFunction m
loadMul sig _ vars False xs =
    do
      t <- foldM f M.empty xs
      return $ G t
    where
      f acc x =
          do
            t <- loadExpr sig vars False x
            return $ mul t acc
loadMul _ pos _ True _ = fail (shows pos "Disallowed bare exponent")

loadCat :: MonadFail m => LoadFunction m
loadCat sig _ vars strict (l : ls) =
    do
      ts <- mapM (loadTerm sig vars strict) (l : ls)
      return $ foldr1 (\a b -> F (Tupl "cat") [a, b]) ts
loadCat _ pos _ _ _ = fail (shows pos "Malformed cat")

loadOper :: MonadFail m => Sig -> Pos -> [Term] -> Bool ->
            Sig.Operator -> [SExpr Pos] -> m Term
loadOper sig pos vars strict (Sig.Enc op) (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat sig pos vars strict butLast
      t' <- loadTerm sig vars strict last
      return $ F (Enc op) [t, t']
loadOper _ pos _ _ (Sig.Enc _) _ = fail (shows pos "Malformed enc")
loadOper sig pos vars strict (Sig.Senc op) (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat sig pos vars strict butLast
      t' <- loadTerm sig vars strict last
      case t' of
        F (Akey _) _ -> fail (shows pos "Expecting a symmetric key")
        _ -> return $ F (Enc op) [t, t']
loadOper _ pos _ _ (Sig.Senc _) _ = fail (shows pos "Malformed senc")
loadOper sig pos vars strict (Sig.Aenc op) (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat sig pos vars strict butLast
      t' <- loadTerm sig vars strict last
      case isAkeyNotInvk t' of
        True -> return $ F (Enc op) [t, t']
        False -> fail (shows pos "Expecting an asymmetric key")
loadOper _ pos _ _ (Sig.Aenc _) _ = fail (shows pos "Malformed aenc")
loadOper sig pos vars strict (Sig.Sign op) (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat sig pos vars strict butLast
      t' <- loadTerm sig vars strict last
      case t' of
        F (Akey _) [F (Invk _) _] -> return $ F (Enc op) [t, t']
        _ -> fail (shows pos "Expecting an asymmetric inverse key")
loadOper _ pos _ _ (Sig.Sign _) _ = fail (shows pos "Malformed sign")
loadOper sig _ vars strict (Sig.Hash op) (l : ls) =
    do
      ts <- mapM (loadTerm sig vars strict) (l : ls)
      return $ F (Hash op) [foldr1 (\a b -> F (Tupl "cat") [a, b]) ts]
loadOper _ pos _ _ (Sig.Hash _) _ = fail (shows pos "Malformed hash")
loadOper sig _ vars strict (Sig.Tupl op len) (l : ls) | length (l : ls) == len =
    do
      ts <- mapM (loadTerm sig vars strict) (l : ls)
      return $ F (Tupl op) ts
loadOper _ pos _ _ (Sig.Tupl _ _) _ = fail (shows pos "Bad tuple length")

-- Could have used init and last, but whatever...
splitLast :: a -> [a] -> ([a], a)
splitLast x xs =
    loop [] x xs
    where
      loop z x [] = (reverse z, x)
      loop z x (y : ys) = loop (x : z) y ys

isAkeyNotInvk :: Term -> Bool
isAkeyNotInvk (F (Akey _) [F (Invk _) _]) = False
isAkeyNotInvk (F (Akey _) _) = True
isAkeyNotInvk _ = False

--   combineVarListSpecs :: [(String,[String])] -> [(String,[String])] -> [(String,[String])]
--   combineVarListSpecs [] vls = vls
--   combineVarListSpecs vls [] = vls
--   combineVarListSpecs ((s, vnames) : vls) ((s', vnames') : vls')
--       | s == s' = (s, (L.nub $ vnames ++ vnames'))
--                   : (combineVarListSpecs vls vls')
--       | otherwise =
--           combineVarListSpecs vls $ (s', vnames') : (combineVarListSpecs [(s, vnames)] vls')

sortNameAndVarName :: Term -> (String,String)
sortNameAndVarName (I (Id(_, name))) = ("mesg", name)
sortNameAndVarName (F (Data sort) [I (Id(_, name))]) = (sort, name)
sortNameAndVarName (F (Akey sort) [I (Id(_, name))]) = (sort, name)
sortNameAndVarName (F Name [I (Id(_, name))]) = ("name", name)
sortNameAndVarName (F Pval [I (Id(_, name))]) = ("pt", name)
sortNameAndVarName (F Chan [I (Id(_, name))]) = ("chan", name)
sortNameAndVarName (F Locn [I (Id(_, name))]) = ("locn", name)
sortNameAndVarName (D (Id(_, name))) = ("strd", name)
sortNameAndVarName (X (Id(_, name))) = ("indx", name)
sortNameAndVarName t = error ("sortNameAndVarName:  Non-var " ++ (show t))

addSortNameToVarListSpec :: (String,String) -> [(String,[String])] -> Maybe [(String,[String])]
addSortNameToVarListSpec (_,_) [] = Nothing
addSortNameToVarListSpec (sn,vn) ((sn',vns) : rest)
    | sn == sn' = Just $ (sn, adjoin vn vns) : rest
    | otherwise =
        do
          added <- addSortNameToVarListSpec (sn,vn) rest
          return $ ((sn',vns) : added)

varListSpecOfVars :: [Term] -> [(String,[String])]
varListSpecOfVars [] = []
varListSpecOfVars (t : rest) =
    let (sn,vn) = sortNameAndVarName t in
    let specRest = varListSpecOfVars rest in
    case addSortNameToVarListSpec (sn,vn) specRest of
      Nothing -> (sn,[vn]) : specRest
      Just added -> added

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
displayVar ctx (F (Data sort) [I x]) = displaySortId sort ctx x
displayVar ctx (F (Akey sort) [I x]) = displaySortId sort ctx x
displayVar ctx (F Name [I x]) = displaySortId "name" ctx x
displayVar ctx (F Pval [I x]) = displaySortId "pval" ctx x
displayVar ctx (F Chan [I x]) = displaySortId "chan" ctx x
displayVar ctx (F Locn [I x]) = displaySortId "locn" ctx x
displayVar ctx (F Base [I x]) = displaySortId "base" ctx x
displayVar ctx t@(G x)
    | isBasisVar x = displaySortId "rndx" ctx (varId t)
    | isGroupVar x = displaySortId "expt" ctx (varId t)
displayVar ctx (D x) = displaySortId "strd" ctx x
displayVar ctx (X x) = displaySortId "indx" ctx x
displayVar _ _ =
    error "Algebra.displayVar: term not a variable with its sort"

displaySortId :: String -> Context -> Id -> (SExpr (), SExpr ())
displaySortId sort ctx x = (displayId ctx x, S () sort)

displayId :: Context -> Id -> SExpr ()
displayId (Context ctx) x =
    case lookup x ctx of
      Nothing ->
          let msg = idName x ++ " in a display context" ++ (show ctx) in
          error $ "Algebra.displayId: Cannot find variable " ++ msg
      Just name -> S () name

-- JDG:  Use this if debugging
--   displayId :: Context -> Id -> SExpr ()
--   displayId (Context ctx) x =
--       case lookup x ctx of
--         Nothing ->
--             let _ = idName x ++ " in a display context" ++ (show ctx) in
--             -- msg ... error $ "Algebra.displayId: Cannot find variable
--             -- " ++ msg
--            S () ("*" ++ idName x ++ "*")
--         Just name -> S () name

notPt :: Term -> Bool
notPt (F Pval [I _]) = False
notPt _ = True

displayTerm :: Context -> Term -> SExpr ()
displayTerm ctx (I x) = displayId ctx x
displayTerm ctx (F (Data _) [I x]) = displayId ctx x
displayTerm ctx (F (Data _) [F Ltk [I x, I y]]) =
    L () [S () "ltk", displayId ctx x, displayId ctx y]
displayTerm ctx (F op@(Data _) [F Bltk [I x, I y]])
  |  x > y = displayTerm ctx (F op [F Bltk [I y, I x]])
  | otherwise = L () [S () "bltk", displayId ctx x, displayId ctx y]
displayTerm ctx (F (Akey _) [t]) =
    case t of
      I x -> displayId ctx x
      F (Invk _) [I x] -> L () [S () "invk", displayId ctx x]
      F Pubk [I x] -> L () [S () "pubk", displayId ctx x]
      F Pubk [C c, I x] -> L () [S () "pubk", Q () c, displayId ctx x]
      F (Invk _) [F Pubk [I x]] -> L () [S () "privk", displayId ctx x]
      F (Invk _) [F Pubk [C c, I x]] ->
          L () [S () "privk", Q () c, displayId ctx x]
      _ -> error ("Algebra.displayAkey: Bad term " ++ show t)
displayTerm ctx (F Name [I x]) = displayId ctx x
displayTerm ctx (F Pval [I x]) = displayId ctx x
displayTerm ctx (F Chan [I x]) = displayId ctx x
displayTerm ctx (F Locn [I x]) = displayId ctx x
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
    displayExpr t
    where
      displayExpr t
          | M.null t = L () [S () "one"]
          | otherwise =
              case factors t of
                [f] -> displayFactor f
                fs -> L () (S () "mul" : map displayFactor fs)
      displayFactor (x, (_, n))
          | n >= 0 = displayId ctx x
          | otherwise = L () [S () "rec", displayId ctx x]
displayTerm _ (C t) = Q () t
displayTerm ctx (F (Tupl "cat") [t0, t1]) =
    L () (S () "cat" : displayTerm ctx t0 : displayList ctx t1)
displayTerm ctx (F (Tupl op) ts) =
    L () (S () op : map (displayTerm ctx) ts)
displayTerm ctx (F (Enc op) [t0, t1]) =
    L () (S () op : displayEnc ctx t0 t1)
displayTerm ctx (F (Hash op) [t]) =
    L () (S () op : displayList ctx t)
displayTerm ctx (D x) = displayId ctx x
displayTerm _ (Z z) = N () z
displayTerm ctx (X x) = displayId ctx x
displayTerm _ (Y z) = N () z
displayTerm _ t = error ("Algebra.displayTerm: Bad term " ++ show t)

displayTermNoPt :: Context -> Term -> SExpr ()
displayTermNoPt ctx (I x) = displayId ctx x
displayTermNoPt ctx (F (Data _) [I x]) = displayId ctx x
displayTermNoPt ctx (F (Data _) [F Ltk [I x, I y]]) =
    L () [S () "ltk", displayId ctx x, displayId ctx y]
displayTermNoPt ctx (F op@(Data _) [F Bltk [I x, I y]])
  |  x > y = displayTermNoPt ctx (F op [F Bltk [I y, I x]])
  | otherwise = L () [S () "bltk", displayId ctx x, displayId ctx y]
displayTermNoPt ctx (F (Akey _) [t]) =
    case t of
      I x -> displayId ctx x
      F (Invk _) [I x] -> L () [S () "invk", displayId ctx x]
      F Pubk [I x] -> L () [S () "pubk", displayId ctx x]
      F Pubk [C c, I x] -> L () [S () "pubk", Q () c, displayId ctx x]
      F (Invk _) [F Pubk [I x]] -> L () [S () "privk", displayId ctx x]
      F (Invk _) [F Pubk [C c, I x]] ->
          L () [S () "privk", Q () c, displayId ctx x]
      _ -> error ("Algebra.displayAkey: Bad term " ++ show t)
displayTermNoPt ctx (F Name [I x]) = displayId ctx x
displayTermNoPt _ (F Pval [I _]) = S () "" -- displayId ctx x
displayTermNoPt ctx (F Chan [I x]) = displayId ctx x
displayTermNoPt ctx (F Locn [I x]) = displayId ctx x
displayTermNoPt ctx (F Base [t]) =
    displayBase t
    where
      displayBase (I x) = displayId ctx x
      displayBase (F Genr []) =
          L () [S () "gen"]
      displayBase (F Exp [t0, G t1]) =
          L () [S () "exp", displayBase t0, displayTerm ctx (G t1)]
      displayBase t = error ("Algebra.displayBase: Bad term " ++ show t)
displayTermNoPt ctx (G t) =
    displayExpr t
    where
      displayExpr t
          | M.null t = L () [S () "one"]
          | otherwise =
              case factors t of
                [f] -> displayFactor f
                fs -> L () (S () "mul" : map displayFactor fs)
      displayFactor (x, (_, n))
          | n >= 0 = displayId ctx x
          | otherwise = L () [S () "rec", displayId ctx x]
displayTermNoPt _ (C t) = Q () t
displayTermNoPt ctx (F (Tupl "cat") [t0, t1]) =
    case t0 of
      (F Pval [I _]) -> displayTermNoPt ctx t1
      _ -> L () (S () "cat" : displayTermNoPt ctx t0 : displayList ctx t1)
displayTermNoPt ctx (F (Tupl op) ts) =
    L () (S () op : map (displayTerm ctx) ts)
displayTermNoPt ctx (F (Enc op) [t0, t1]) =
    L () (S () op : displayEnc ctx t0 t1)
displayTermNoPt ctx (F (Hash op) [t]) =
    L () (S () op : displayList ctx t)
displayTermNoPt ctx (D x) = displayId ctx x
displayTermNoPt _ (Z z) = N () z
displayTermNoPt ctx (X x) = displayId ctx x
displayTermNoPt _ (Y z) = N () z
displayTermNoPt _ t = error ("Algebra.displayTermNoPt: Bad term " ++ show t)

displayList :: Context -> Term -> [SExpr ()]
displayList ctx (F (Tupl "cat") [t0, t1]) =
  displayTerm ctx t0 : displayList ctx t1
displayList ctx t = [displayTerm ctx t]

displayEnc :: Context -> Term -> Term -> [SExpr ()]
displayEnc ctx (F (Tupl "cat") [t0, t1]) t =
  displayTerm ctx t0 : displayEnc ctx t1 t
displayEnc ctx t0 t1 = [displayTerm ctx t0, displayTerm ctx t1]

displayEnv :: Context -> Context -> Env -> [SExpr ()]
displayEnv ctx ctx' (Env (_, r)) =
    map (\(x, t) -> L () [displayTerm ctx x, displayTerm ctx'' t]) r'
    where
      r' = map (\(x, t) -> (I x, inferSort t)) $ M.assocs r
      ctx'' = addToContext ctx' (map snd r')

-- displaySubst c s displays a substitution s in context c, where some
-- variables that occur in s might not be in c.  Enough sort
-- inference is performed so as to allow the extension of the context.
displaySubst :: Context -> Subst -> [SExpr ()]
displaySubst ctx (Subst r) =
    map (\(x, t) -> L () [displayTerm ctx' x, displayTerm ctx' t]) r'
    where
      r' = map (\(x, t) -> (I x, inferSort t)) $ M.assocs r
      ctx' = foldl (\ctx (x, t) -> addToContext ctx [x, t]) ctx r'

inferSort :: Term -> Term
inferSort t@(F (Invk op) _) = F (Akey op) [t]
inferSort t@(F Pubk _) = F (Akey "akey") [t]
inferSort t@(F Ltk _) = F (Data "skey") [t]
inferSort t@(F Bltk _) = F (Data "skey") [t]
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
