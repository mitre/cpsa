-- Basic Crypto Algebra implementation

-- The module implements a many-sorted algebra, but is used as an
-- order-sorted algebra.  It exports a name, and the origin used to
-- generate variables.

-- To support security goals, the message algebra has been augmented
-- with support for variables of sort strd and integers.  The
-- constructor D is used as N is taken for numbers in S-Expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

--------------------------------------------------------------------

-- The Basic Crypto Order-Sorted Signature is

-- Sorts: mesg, text, data, name, skey, akey, chan, locn, and string
--
-- Subsorts: text, data, name, skey, akey, chan < mesg
--
-- Operations:
--   cat : mesg X mesg -> mesg               Pairing
--   enc : mesg X mesg -> mesg               Encryption
--   hash : mesg -> mesg                     Hashing
--   string : mesg                           Tag constants
--   ltk : name X name -> skey               Long term shared key
--   pubk : name -> akey                     Public key of principal
--   pubk : string X name -> akey            Tagged public key of principal
--   invk : akey -> akey                     Inverse of asymmetric key
--
-- Atoms: messages of sort text, data, name, skey, akey, locn, and chan.

-- Variables of sort string are forbidden.

-- The implementation exploits the isomorphism between order-sorted
-- algebras and many-sorted algebras by adding inclusion operations to
-- produce an equivalent Basic Crypto Many-Sorted Signature.  There is
-- an inclusion operation for each subsort of mesg.

-- Sorts: mesg, text, data, name, skey, akey, chan, and string
--
-- Operations:
--   cat : mesg X mesg -> mesg               Pairing
--   enc : mesg X mesg -> mesg               Encryption
--   hash : mesg -> mesg                     Hashing
--   string : mesg                           Tag constants
--   ltk : name X name -> skey               Long term shared key
--   pubk : name -> akey                     Public key of principal
--   pubk : string X name -> akey            Tagged public key of principal
--   invk : akey -> akey                     Inverse of asymmetric key
--   text : text -> mesg                     Sort text inclusion
--   data : data -> mesg                     Sort date inclusion
--   name : name -> mesg                     Sort name inclusion
--   skey : skey -> mesg                     Sort skey inclusion
--   akey : akey -> mesg                     Sort akey inclusion
--   chan : chan -> mesg                     Sort chan inclusion
--   locn : locn -> mesg                     Sort locn inclusion

-- In both algebras, invk(invk(t)) = t for all t of sort akey

{-# LANGUAGE CPP #-}

#if !(MIN_VERSION_base(4,13,0))
#define MonadFail Monad
#endif

module CPSA.Algebra (name,

    Gen,
    origin,
    gmerge,
    clone,
    loadVars,
    newVar,
    varName,

    Term,
    isVar,
    isAcquiredVar,
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
    decryptionKey,
    decompose,
    buildable,
    components,
    encryptions,
    escapeSet,
    loadTerm,
    loadLocnTerm,
    indxOfInt,

    Place (..),
    places,
    carriedPlaces,
    replace,
    ancestors,

    Subst,
    emptySubst,
    disjointDom,
    substitute,
    unify,
    compose,

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
import CPSA.Lib.Utilities (replaceNth, adjoin)
import CPSA.Lib.SExpr (SExpr(..), Pos, annotation)

name :: String
name = "basic"

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

newtype Gen = Gen (Integer) deriving Show

origin :: Gen
origin = Gen (0)

gmerge :: Gen -> Gen -> Gen
gmerge (Gen i) (Gen j) = Gen $ max i j

freshId :: Gen -> String -> (Gen, Id)
freshId (Gen i) name = (Gen (i + 1), Id (i, name))

cloneId :: Gen -> Id -> (Gen, Id)
cloneId gen x = freshId gen (idName x)

-- Operations other than the tag constant constructor
data Symbol
    = Data String               -- Atoms
    | Akey String               -- Asymmetric keys
    | Name                      -- Principal
    | Pval                      -- Point at which a store occurs
    | Ltk                       -- Long term shared symmetric key
    | Invk String               -- Inverse of asymmetric key
    | Pubk                      -- Public asymmetric key of a principal
    | Chan                      -- Channel
    | Locn                      -- Location
    | Tupl String               -- Term tupling
    | Enc String                -- Encryption
    | Hash String               -- Hashing
      deriving (Show, Eq, Ord)

-- A Basic Crypto Algebra Term

data Term
    = I !Id
    | C !String                 -- Tag constants
    | F !Symbol ![Term]
    | D !Id                     -- Strd variable
    | Z Int                     -- Strd constant
    | X !Id                     -- Indx variable
    | Y Int                     -- Indx constant
      deriving (Show, Eq, Ord)

-- In this algebra (F Invk [F Invk [t]]) == t is an axiom

-- Basic terms are introduced by defining a function used to decide if
-- a term is well-formed.  The context of an occurrence of an identifier
-- determines its sort.  A term that contains just an identifier and its
-- sort information is called a variable.  The sort of a variable is
-- one of mesg, text, data, name, skey, and akey.

-- Terms that represent algebra variables.
isVar :: Term -> Bool
isVar (I _) = True           -- Sort: mesg
isVar (F s [I _]) = varSym s
isVar _ = False

varSym :: Symbol -> Bool
varSym (Data _) = True
varSym (Akey _) = True
varSym Name = True
varSym Pval = True
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
varId (F Pval [I x]) = x
varId (F Chan [I x]) = x
varId (F Locn [I x]) = x
varId (D x) = x
varId (X x) = x
varId _ = error "Algebra.varId: term not a variable with its sort"

isAcquiredVar :: Term -> Bool
isAcquiredVar (I _) = True
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

-- A term is well-formed if it is in the language defined by the
-- following grammar, and variables occur at positions within the term
-- in a way that allows each variable to be assigned one sort.
--
-- The start symbol is T, for all well-formed terms.  Terminal symbol
-- I is for variables and terminal symbol C is for quoted strings.
-- The non-terminal symbols are B, K, and T.  Symbol B is for base
-- sorted terms, and K is for asymmetric keys.
--
--     T ::= I | C | B | cat(T, T) | enc(T, T) | hash(T)
--
--     B ::= text(I) | data(I) | name(I) | pval(I) | skey(I)
--        |  skey(I) | skey(ltk(I, I)) | akey(K)
--
--     K ::= I | pubk(I) | invk(I) | invk(pubk(I))

-- Note that a channel or location variable is not considered a well formed term.

-- termWellFormed checks the structure and sort condition.
termWellFormed :: VarEnv -> Term -> Maybe VarEnv
termWellFormed xts t@(I x) =
    extendVarEnv xts x t        -- Mesg variable
termWellFormed xts t@(F (Data _) [I x]) =
    extendVarEnv xts x t        -- Data variable
termWellFormed xts (F (Data "skey") [F Ltk [I x, I y]]) =
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
termWellFormed xts (C _) =
    Just xts                    -- Tags
termWellFormed xts (F (Tupl _) ts) =
    foldM termWellFormed xts ts -- tupling
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
isAtom (F s _) = varSym s
isAtom _ = False

-- Does a variable occur in a term?
occursIn :: Term -> Term -> Bool
occursIn t t' | isVar t =
  recur (I $ varId t) t'
  where
    recur t t' =
      t == t' ||
      case t' of
        F _ u -> any (recur t) u
        _ -> False
occursIn t _ = error $ "Algebra.occursIn: Bad variable " ++ show t

-- Fold f through a term applying it to each variable in the term.
foldVars :: (a -> Term -> a) -> a -> Term -> a
foldVars f acc t@(I _) = f acc t          -- Mesg variable
foldVars f acc t@(F (Data _) [I _]) = f acc t -- Data variable
foldVars f acc (F (Data _) [F Ltk [I x, I y]]) =
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
foldVars _ acc (C _) = acc                -- Tags
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
foldCarriedTerms f acc t = f acc t     -- atoms and tags

-- Is a term carried by another term?
carriedBy :: Term -> Term -> Bool
carriedBy t t' =
    t == t' ||
      case t' of
        F (Tupl _) ts -> any (carriedBy t) ts
        F (Enc _) [t0, _] -> carriedBy t t0
        _ -> False

-- The key used to decrypt an encrypted term, otherwise Nothing.
decryptionKey :: Term -> Maybe Term
decryptionKey (F (Enc _) [_, t]) = Just (inv t)
decryptionKey _ = Nothing

buildable :: Set Term -> Set Term -> Term -> Bool
buildable knowns unguessable term =
    ba term
    where
      ba (I _) = True           -- A mesg sorted variable is always buildable
      ba (C _) = True           -- and so is a tag
      ba (F (Tupl _) ts) =
          all ba ts
      ba t@(F (Enc _) [t0, t1]) =
          S.member t knowns || ba t0 && ba t1
      ba t@(F (Hash _) [t1]) =
          S.member t knowns || ba t1
      ba t = isAtom t && S.notMember t unguessable

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
      loop unguessable knowns old (t : todo) =
          loop (S.delete t unguessable) (S.delete t knowns) old todo
      -- Decat
      decat :: Term -> Set Term -> Set Term
      decat (F (Tupl _) ts) s = foldr decat s ts
      decat t s = S.insert t s

-- Inverts an asymmetric key
inv :: Term -> Term
inv (F (Akey op) [F (Invk _) [t]]) = F (Akey op) [t]
inv (F (Akey op) [t]) = F (Akey op) [F (Invk op) [t]]
inv t@(F _ _) = t
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
    f t []
    where
      f (F (Tupl _) ts) acc =
        foldr f acc ts
      f t@(F (Enc _) [t', t'']) acc =
        f t' (adjoin (t, [t'']) acc)
      f t@(F (Hash _) [t']) acc =
        adjoin (t, [t']) acc
      f _ acc = acc

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

-- Places

-- A place names a one subterm within a term.  It is a list of
-- integers giving a path through a term to that named subterm.  Each
-- integer in the list identifies the subterm in a function
-- application on the path to the named subterm.  The integer is the
-- index of the subterm in the application's list of terms.

newtype Place = Place [Int] deriving Show

-- Returns the places a variable occurs within another term.
places :: Term -> Term -> [Place]
places target source =
    f [] [] source
    where
      f paths path source
          | I (varId target) == source = Place (reverse path) : paths
      f paths path (F _ u) =
          g paths path 0 u
      f paths _ _ = paths
      g paths _ _ [] = paths
      g paths path i (t : u) =
          g (f paths (i: path) t) path (i + 1) u

-- Replace a variable within a term at a given place.
replace :: Term -> Place -> Term -> Term
replace target (Place ints) source =
    loop ints source
    where
      loop [] _ = I (varId target)
      loop (i : path) (F s u) =
          F s (replaceNth (loop path (u !! i)) i u)
      loop _ _ = error "Algebra.replace: Bad path to variable"

-- Returns the places a term is carried by another term.
carriedPlaces :: Term -> Term -> [Place]
carriedPlaces target source =
    f [] [] source
    where
      f paths path source
          | target == source = Place (reverse path) : paths
      f paths path (F (Tupl _) ts) =
          foldr g paths (zip [0..] ts)
          where
            g (i, t) paths = f paths (i : path) t
      f paths path (F (Enc _) [t, _]) =
          f paths (0 : path) t
      f paths _ _ = paths

-- Return the ancestors of the term at the given place.
ancestors :: Term -> Place -> [Term]
ancestors source (Place ints) =
    loop [] ints source
    where
      loop ts [] _ = ts
      loop ts (i: path) t@(F _ u) =
          loop (t : ts) path (u !! i)
      loop _ _ _ = error "Algebra.ancestors: Bad path to term"

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

-- Functions used in both unification and matching

type IdMap = Map Id Term

emptyIdMap :: IdMap
emptyIdMap = M.empty

-- Apply a substitution to a term
idSubst :: IdMap -> Term -> Term
idSubst subst (I x) =
    M.findWithDefault (I x) x subst
idSubst _ t@(C _) = t
idSubst subst (F (Invk op) [t]) =
    case idSubst subst t of
      F (Invk _) [t] -> t      -- Apply axiom
      t -> F (Invk op) [t]
idSubst subst (F s u) =
    F s (map (idSubst subst) u)
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
idMapped subst (D x) = M.member x subst
idMapped _ (Z _) = True
idMapped subst (X x) = M.member x subst
idMapped _ (Y _) = True

-- Unification and substitution

newtype Subst = Subst IdMap deriving (Eq, Ord, Show)

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
chase _ t = t

chaseInvk :: Subst -> String -> Term -> Term
chaseInvk (Subst s) op (I x) =
    case M.lookup x s of
      Nothing -> F (Invk op) [I x]
      Just t -> chaseInvk (Subst s) op t
chaseInvk s _ (F (Invk _) [t]) = chase s t
chaseInvk _ op t = F (Invk op) [t]

-- Does x occur in t?
occurs :: Id -> Term -> Bool
occurs x (I y) = x == y
occurs _ (C _) = False
occurs x (F _ u) = any (occurs x) u
occurs x (D y) = x == y
occurs _ (Z _) = False
occurs x (X y) = x == y
occurs _ (Y _) = False

unifyChase :: Term -> Term -> Subst -> Maybe Subst
unifyChase t t' s = unifyTerms (chase s t) (chase s t') s

unifyTerms :: Term -> Term -> Subst -> Maybe Subst
unifyTerms (I x) (I y) (Subst s)
    | x == y = Just (Subst s)
    | otherwise = Just (Subst $ M.insert x (I y) s)
unifyTerms (I x) t (Subst s)
    | occurs x t = Nothing
    | otherwise = Just (Subst $ M.insert x t s)
unifyTerms t (I x) s = unifyTerms (I x) t s
unifyTerms (C c) (C c') s
    | c == c' = Just s
    | otherwise = Nothing
unifyTerms (F (Invk op) [I x]) (F Pubk [I y]) s =
    unifyTerms (I x) (F (Invk op) [F Pubk [I y]]) s
unifyTerms (F (Invk op) [I x]) (F Pubk [C c, I y]) s =
    unifyTerms (I x) (F (Invk op) [F Pubk [C c, I y]]) s
unifyTerms (F Pubk [I x]) (F (Invk op) [I y]) s =
    unifyTerms (I y) (F (Invk op) [F Pubk [I x]]) s
unifyTerms (F Pubk [C c, I x]) (F (Invk op) [I y]) s =
    unifyTerms (I y) (F (Invk op) [F Pubk [C c, I x]]) s
unifyTerms (F sym u) (F sym' u') s
    | sym == sym' = unifyTermLists u u' s
    | otherwise = Nothing
unifyTerms (D x) (D y) (Subst s)
    | x == y = Just (Subst s)
    | otherwise = Just (Subst $ M.insert x (D y) s)
unifyTerms (D x) (Z p) (Subst s) =
    Just (Subst $ M.insert x (Z p) s)
unifyTerms t (D x) s = unifyTerms (D x) t s
unifyTerms (Z p) (Z p') s
    | p == p' = Just s
    | otherwise = Nothing
unifyTerms _ _ _ = Nothing

unifyTermLists :: [Term] -> [Term] -> Subst -> Maybe Subst
unifyTermLists [] [] s = Just s
unifyTermLists (t : u) (t' : u') s =
    maybe Nothing (unifyTermLists u u') (unifyChase t t' s)
unifyTermLists _ _ _ = Nothing

-- The exported unifier converts the internal representation of a
-- substitution into the external form using chaseMap.

unifyI :: Term -> Term -> Subst -> Maybe Subst
unifyI t t' s =
    do
      s <- unifyChase t t' s
      return $ chaseMap s

unify :: Term -> Term -> (Gen, Subst) -> [(Gen, Subst)]
unify t t' (g, s) =
  maybe [] (\s -> [(g, s)]) $ unifyI t t' s

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
substChase subst t =
    case chase subst t of
      t@(I _) -> t
      t@(C _) -> t
      F (Invk op) [t] ->
          case substChase subst t of
            F (Invk _) [t] -> t           -- Apply axiom
            t -> F (Invk op) [t]
      F s u ->
          F s (map (substChase subst) u)
      t@(D _) -> t
      t@(Z _) -> t
      t@(X _) -> t
      t@(Y _) -> t

-- Matching and instantiation

newtype Env = Env IdMap deriving (Eq, Ord, Show)

-- An environment may contain an explicit identity mapping, whereas a
-- substitution is erroneous if it has one.

emptyEnv :: Env
emptyEnv = Env emptyIdMap

-- Apply a substitution created my matching
instantiate :: Env -> Term -> Term
instantiate (Env r) t = idSubst r t

-- Is every variable in t in the domain of r?
matched :: Env -> Term -> Bool
matched (Env r) t = idMapped r t

-- Apply a substitution to the range of an environment
substUpdate :: Env -> Subst -> Env
substUpdate (Env r) s =
  Env $ M.map (substitute s) r

-- Matching

match ::  Term -> Term -> (Gen, Env) -> [(Gen, Env)]
match t t' (g, e) =
  maybe [] (\e -> [(g, e)]) $ matchI t t' e

-- match ::  Term -> Term -> (Gen, Env) -> [(Gen, Env)]
-- match x y e@(g, e)
--   | badGen g x =
--       error ("match: " ++ show g ++ ": " ++ show x)
--   | badGen g y =
--       error ("match: " ++ show g ++ ": " ++ show y)
--   | otherwise =
--       maybe [] (\e -> [(g, e)]) $ matchI t t' e

-- The matcher has the property that when pattern P and term T match
-- then instantiate (match P T emptyEnv) P = T.
matchI ::  Term -> Term -> Env -> Maybe Env
matchI (I x) t (Env r) =
    case M.lookup x r of
      Nothing -> Just $ Env $ M.insert x t r
      Just t' -> if t == t' then Just $ Env r else Nothing
matchI (C c) (C c') r = if c == c' then Just r else Nothing
matchI (F s u) (F s' u') r
    | s == s' = matchLists u u' r
matchI (F (Invk op) [t]) t' r =
    matchI t (F (Invk op) [t']) r
matchI (D x) t (Env r) =
    case M.lookup x r of
      Nothing -> Just $ Env $ M.insert x t r
      Just t' -> if t == t' then Just $ Env r else Nothing
matchI (Z p) (Z p') r = if p == p' then Just r else Nothing
matchI (X x) t (Env r) =
    case M.lookup x r of
      Nothing -> Just $ Env $ M.insert x t r
      Just t' -> if t == t' then Just $ Env r else Nothing
matchI (Y p) (Y p') r = if p == p' then Just r else Nothing
matchI _ _ _ = Nothing

matchLists :: [Term] -> [Term] -> Env -> Maybe Env
matchLists [] [] r = Just r
matchLists (t : u) (t' : u') r =
    maybe Nothing (matchLists u u') (matchI t t' r)
matchLists _ _ _ = Nothing

-- Cast an environment into a substitution by filtering out trivial
-- bindings.

substitution :: Env -> Subst
substitution (Env r) =
    Subst $ M.filterWithKey nonTrivialBinding r

-- Find bound above all the strand indices i in strand values Z i in
-- values in the environment
strandBoundEnv :: Env -> Int
strandBoundEnv (Env map) =
    M.foldl f 0 map
     where
       f bnd (Z i) = max bnd (i+1)
       f bnd _ = bnd

-- Add type information to an environment, and return it as a list of
-- associations.

reify :: [Term] -> Env -> [(Term, Term)]
reify domain (Env env) =
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
      loop (D x : _) (y, t)
          | x == y = (D x, t)
      loop (X x : _) (y, t)
          | x == y = (X x, t)
      loop (_ : domain) pair = loop domain pair

strdMatch ::  Term -> Int -> (Gen, Env) -> [(Gen, Env)]
strdMatch t t' (g, e) =
       maybe [] (\e -> [(g, e)]) $ strdMatchI t t' e

strdMatchI ::  Term -> Int -> Env -> Maybe Env
strdMatchI t p env = matchI t (Z p) env

strdLookup :: Env -> Term -> Maybe Int
strdLookup env t =
  case instantiate env t of
    Z p -> Just p
    _ -> Nothing

strdUpdate :: Env -> (Int -> Int) -> Env
strdUpdate (Env e) f =
  Env $ M.map h e
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
indxUpdate (Env e) f =
  Env $ M.map h e
  where
    h (Y z) = Y $ f z
    h t = t

indxOfInt :: Int -> Term
indxOfInt i = Y i

-- Term specific loading functions

loadVars :: MonadFail m => Gen -> [SExpr Pos] -> m (Gen, [Term])
loadVars gen sexprs =
    do
      pairs <- mapM loadVarPair sexprs
      (g, vars) <- foldM loadVar (gen, []) (concat pairs)
      return (g, reverse vars)

loadVarPair :: MonadFail m => SExpr Pos -> m [(SExpr Pos, SExpr Pos)]
loadVarPair (L _ (x:y:xs)) =
    let (t:vs) = reverse (x:y:xs) in
    return [(v,t) | v <- reverse vs]
loadVarPair x = fail (shows (annotation x) "Bad variable declaration")

loadVar :: MonadFail m => (Gen, [Term]) -> (SExpr Pos, SExpr Pos) ->
           m (Gen, [Term])
loadVar (gen, vars) (S pos name, S pos' sort) =
    case loadLookup pos vars name of
      Right _ ->
          fail (shows pos "Duplicate variable declaration for " ++ name)
      Left _ ->
          do
            let (gen', x) = freshId gen name
            p <- mkVar pos' sort x
            return (gen', p : vars)
loadVar _ (x,_) = fail (shows (annotation x) "Bad variable syntax")

mkVar :: MonadFail m => Pos -> String -> Id -> m Term
mkVar pos sort x
  | sort == "mesg" = return $ I x
  | sort == "text" = return $ F (Data "text") [I x]
  | sort == "data" = return $ F (Data "data") [I x]
  | sort == "name" = return $ F Name [I x]
  | sort == "pval" = return $ F Pval [I x]
  | sort == "skey" = return $ F (Data "skey") [I x]
  | sort == "akey" = return $ F (Akey "akey") [I x]
  | sort == "chan" = return $ F Chan [I x]
  | sort == "locn" = return $ F Locn [I x]
  | sort == "strd" = return $ D x
  | sort == "indx" = return $ X x
  | otherwise = fail (shows pos "Sort " ++ sort ++ " not recognized")

newVar :: Gen -> String -> String -> (Gen, Term)
newVar g varName varSort =
    let (g', x) = freshId g varName in
    (g', mkVarUnfailingly varSort x)

mkVarUnfailingly :: String -> Id -> Term
mkVarUnfailingly sort x
  | sort == "mesg" =  I x
  | sort == "text" =  F (Data "text") [I x]
  | sort == "data" =  F (Data "data") [I x]
  | sort == "name" =  F Name [I x]
  | sort == "pval" =  F Pval [I x]
  | sort == "skey" =  F (Data "skey") [I x]
  | sort == "akey" =  F (Akey "akey") [I x]
  | sort == "chan" =  F Chan [I x]
  | sort == "locn" =  F Locn [I x]
  | sort == "strd" =  D x
  | sort == "indx" =  X x
  | otherwise =  I x    -- Default:  Var of sort mesg

varName :: Term -> String
varName t = idName (varId t)

loadLookup :: Pos -> [Term] -> String -> Either String Term
loadLookup pos [] name = Left (shows pos $ "Identifier " ++ name ++ " unknown")
loadLookup pos (t : u) name =
    let name' = idName (varId t) in
    if name' == name then Right t else loadLookup pos u name

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
loadTerm :: MonadFail m => [Term] -> SExpr Pos -> m Term
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

loadDispatch :: MonadFail m => [(String, LoadFunction m)]
loadDispatch =
    [("pubk", loadPubk)
    ,("privk", loadPrivk)
    ,("invk", loadInvk)
    ,("ltk", loadLtk)
    ,("cat", loadCat)
    ,("enc", loadEnc)
    ,("hash", loadHash)
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

loadLocnTerm :: MonadFail m => Gen -> SExpr Pos -> SExpr Pos -> Term -> m (Gen, Term, Term)
loadLocnTerm gen (S pos ptStr) (S pos' pvalStr) t =
    do
      (gen', vars) <- loadVar (gen, []) (S pos ptStr, S pos' pvalStr)
      case vars of
        []     -> fail (shows pos "No variable generated by loadVar in loadLocnTerm")
        pt : _ -> return (gen', pt, locnMesg pt t)
loadLocnTerm _ _ _ _ =
    fail "loadLocnTerm:  Call only with SExprs that are really Strings"

-- Atom constructors: pubk privk invk ltk

loadPubk :: MonadFail m => LoadFunction m
loadPubk _ vars [S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [I $ varId t]]
loadPubk _ vars [Q _ c, S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [C c, I $ varId t]]
loadPubk pos _ _ = fail (shows pos "Malformed pubk")

loadPrivk :: MonadFail m => LoadFunction m
loadPrivk _ vars [S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [I $ varId t]]]
loadPrivk _ vars [Q _ c, S pos s] =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [C c, I $ varId t]]]
loadPrivk pos _ _ = fail (shows pos "Malformed privk")

loadInvk :: MonadFail m => LoadFunction m
loadInvk _ vars [S pos s] =
    do
      (op, t) <- loadLookupAkey pos vars s
      return $ F (Akey op) [F (Invk op) [I $ varId t]]
loadInvk _ vars [L _ [S _ pubk, S pos s]]
  | pubk == "pubk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [I $ varId t]]]
loadInvk _ vars [L _ [S _ pubk, Q _ c, S pos s]]
  | pubk == "pubk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F (Invk "akey") [F Pubk [C c, I $ varId t]]]
loadInvk _ vars [L _ [S _ privk, S pos s]]
  | privk == "privk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [I $ varId t]]
loadInvk _ vars [L _ [S _ privk, Q _ c, S pos s]]
  | privk == "privk" =
    do
      t <- loadLookupName pos vars s
      return $ F (Akey "akey") [F Pubk [C c, I $ varId t]]
loadInvk _ vars [L _ [S _ invk, t]]
  | invk == "invk" =
    do
      a <- loadTerm vars t
      case a of
        F (Akey _) _ -> return a
        _ -> fail (shows (annotation t) "Expecting an akey")
loadInvk pos _ _ = fail (shows pos "Malformed invk")

loadLtk :: MonadFail m => LoadFunction m
loadLtk _ vars [S pos s, S pos' s'] =
    do
      t <- loadLookupName pos vars s
      t' <- loadLookupName pos' vars s'
      return $ F (Data "skey") [F Ltk [I $ varId t, I $ varId t']]
loadLtk pos _ _ = fail (shows pos "Malformed ltk")

-- Term constructors: cat enc

loadCat :: MonadFail m => LoadFunction m
loadCat _ vars (l : ls) =
    do
      ts <- mapM (loadTerm vars) (l : ls)
      return $ foldr1 (\a b -> F (Tupl "cat") [a, b]) ts
loadCat pos _ _ = fail (shows pos "Malformed cat")

loadEnc :: MonadFail m => LoadFunction m
loadEnc pos vars (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat pos vars butLast
      t' <- loadTerm vars last
      return $ F (Enc "enc") [t, t']
loadEnc pos _ _ = fail (shows pos "Malformed enc")

splitLast :: a -> [a] -> ([a], a)
splitLast x xs =
    loop [] x xs
    where
      loop z x [] = (reverse z, x)
      loop z x (y : ys) = loop (x : z) y ys

loadHash :: MonadFail m => LoadFunction m
loadHash _ vars (l : ls) =
   do
     ts <- mapM (loadTerm vars) (l : ls)
     return $ F (Hash "hash") [foldr1 (\a b -> F (Tupl "cat") [a, b]) ts]
loadHash pos _ _ = fail (shows pos "Malformed hash")

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
displayVar ctx (D x) = displaySortId "strd" ctx x
displayVar ctx (X x) = displaySortId "indx" ctx x
displayVar _ _ =
    error "Algebra.displayVar: term not a variable with its sort"

displaySortId :: String -> Context -> Id -> (SExpr (), SExpr ())
displaySortId sort ctx x = (displayId ctx x, S () sort)

-- JDG:  Restore this later !!!
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
displayEnv ctx ctx' (Env r) =
    map (\(x, t) -> L () [displayTerm ctx x, displayTerm ctx' t]) r'
    where
      r' = map (\(x, t) -> (I x, inferSort t)) $ M.assocs r

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
