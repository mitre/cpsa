-- CPSA terms and sorts

module CPSA.ZSL.Term where

import Data.Maybe

import CPSA.Lib.SExpr (SExpr(S, L))

-- Variables

type Var = String

-- Terms

data Term =
  Atom Var
  | Tupl [Term]
  | Enc Term Term
  | Hash Term
  | Pubk Term
  | Invk Term
  | Ltk Term Term
  deriving (Eq, Show)

-- Substutute a term for a variable in a term

substTerm :: Term -> Var -> Term -> Term
substTerm (Atom v') v t | v == v' = t | otherwise = Atom v'
substTerm (Tupl ts) v t = Tupl (map (\t' -> substTerm t' v t) ts)
substTerm (Enc t1 t2) v t = Enc (substTerm t1 v t) (substTerm t2 v t)
substTerm (Hash t') v t = Hash (substTerm t' v t)
substTerm (Pubk t') v t = Pubk (substTerm t' v t)
substTerm (Invk t') v t = Invk (substTerm t' v t)
substTerm (Ltk t1 t2) v t = Ltk (substTerm t1 v t) (substTerm t2 v t)

-- Check whether a variable occurs in a term

occursIn :: Var -> Term -> Bool
occursIn v (Atom v') = v == v'
occursIn v (Tupl ts) = foldl (\acc t -> acc || occursIn v t) False ts
occursIn v (Enc t1 t2) = occursIn v t1 || occursIn v t2
occursIn v (Hash t) = occursIn v t
occursIn v (Pubk t) = occursIn v t
occursIn v (Invk t) = occursIn v t
occursIn v (Ltk t1 t2) = occursIn v t1 || occursIn v t2

-- Convert an S-expression into a term

termOfSExpr :: SExpr a -> Maybe Term
termOfSExpr (S _ v) = Just (Atom v)
termOfSExpr (L _ (S _ "cat" : sexprs)) = do
  ts <- mapM termOfSExpr sexprs
  Just (Tupl ts)
termOfSExpr (L _ [S _ "enc", sexpr1, sexpr2]) = do
  t1 <- termOfSExpr sexpr1
  t2 <- termOfSExpr sexpr2
  Just (Enc t1 t2)
termOfSExpr (L _ [S _ "hash", sexpr]) = do
  t <- termOfSExpr sexpr
  Just (Hash t)
termOfSExpr (L _ [S _ "pubk", sexpr]) = do
  t <- termOfSExpr sexpr
  Just (Pubk t)
termOfSExpr (L _ [S _ "invk", sexpr]) = do
  t <- termOfSExpr sexpr
  Just (Invk t)
termOfSExpr (L _ [S _ "privk", sexpr]) = do
  t <- termOfSExpr sexpr
  Just (Invk (Pubk t))
termOfSExpr (L _ [S _ "ltk", sexpr1, sexpr2]) = do
  t1 <- termOfSExpr sexpr1
  t2 <- termOfSExpr sexpr2
  Just (Ltk t1 t2)
termOfSExpr _ = Nothing

-- Convert a term into an S-expression

sexprOfTerm :: Term -> SExpr ()
sexprOfTerm (Atom v) = S () v
sexprOfTerm (Tupl ts) = L () (S () "cat" : map sexprOfTerm ts)
sexprOfTerm (Enc t1 t2) = L () [S () "enc", sexprOfTerm t1, sexprOfTerm t2]
sexprOfTerm (Hash t) = L () [S () "hash", sexprOfTerm t]
sexprOfTerm (Pubk t) = L () [S () "pubk", sexprOfTerm t]
sexprOfTerm (Invk t) = L () [S () "invk", sexprOfTerm t]
sexprOfTerm (Ltk t1 t2) = L () [S () "ltk", sexprOfTerm t1, sexprOfTerm t2]

-- Sorts

data Sort = Text | Data | Name | Skey | Akey | Mesg deriving (Eq, Show)

-- Mapping from strings to sorts

sortOfStr :: String -> Maybe Sort
sortOfStr "text" = Just Text
sortOfStr "data" = Just Data
sortOfStr "name" = Just Name
sortOfStr "skey" = Just Skey
sortOfStr "akey" = Just Akey
sortOfStr "mesg" = Just Mesg
sortOfStr _ = Nothing

-- A predicate that defines when the first sort contains the second

sortIncl :: Sort -> Sort -> Bool
sortIncl Text Text = True
sortIncl Data Data = True
sortIncl Name Name = True
sortIncl Skey Skey = True
sortIncl Akey Akey = True
sortIncl Mesg _    = True
sortIncl _    _    = False

-- Partial maps from variables to sorts

type SortMap = Var -> Maybe Sort

-- The empty sort map

mapEmpty :: SortMap
mapEmpty = \_ -> Nothing

-- Update a sort map with a new mapping

mapUpdate :: SortMap -> Var -> Sort -> SortMap
mapUpdate m v s = \x -> if x == v then Just s else m x

-- Query a sort map for the sort of a term

sortOf :: SortMap -> Term -> Maybe Sort
sortOf m (Atom v) = m v
sortOf m (Tupl ts)
  | foldl (\acc t -> acc && isJust (sortOf m t)) True ts = Just Mesg
  | otherwise = Nothing
sortOf m (Enc t1 t2)
  | isJust (sortOf m t1) && isJust (sortOf m t2) = Just Mesg
  | otherwise = Nothing
sortOf m (Hash t)
  | isJust (sortOf m t) = Just Mesg
  | otherwise = Nothing
sortOf m (Pubk (Atom v))
  | m v == Just Name = Just Akey
  | otherwise = Nothing
sortOf _ (Pubk _) = Nothing
sortOf m (Invk t)
  | sortOf m t == Just Akey = Just Akey
  | otherwise = Nothing
sortOf m (Ltk (Atom v1) (Atom v2))
  | m v1 == Just Name && m v2 == Just Name = Just Skey
  | otherwise = Nothing
sortOf _ (Ltk _ _) = Nothing

-- Determine whether a term is well-formed (has a well-defined sort)
-- relative to a sort map

termWf :: SortMap -> Term -> Bool
termWf m t = isJust (sortOf m t)

-- Generate a sort map from a list of variable-sort pairs

toSortMap :: [(Var, Sort)] -> SortMap
toSortMap = foldl (\m x -> mapUpdate m (fst x) (snd x)) mapEmpty
