-- Unification and matching in a simple Diffie-Hellman algebra

module SimpleDiffieHellman where

-- Equational unification and matching in an algebra with the
-- following equation is used to analyze protocols that make use of
-- the Diffie-Hellman problem.
--
--      exp(exp(x, y), z) = exp(exp(x, z), y)
--
-- The module shows how to perform the unification and matching.

import Char(isDigit, isAlpha)

-- TERMS

-- Variables are just integers so that it is easy to freshly generate
-- them.

type Var = Int

data Term                       -- A term is
    = V Var                     -- a variable, or a
    | F String [Term]           -- function symbol and a list of terms

-- Equality modulo the equation: exp(exp(x, y), z) = exp(exp(x, z), y).
instance Eq Term where
    (V x) == (V y) = x == y
    (F "exp" [F "exp" [x, y], z]) == (F "exp" [F "exp" [x', y'], z']) =
         x == x' && y == y' && z == z' ||
         x == x' && y == z' && z == y'
    (F sym ts) == (F sym' ts') = sym == sym' && ts == ts'
    _ == _ = False

-- SUBSTITUTIONS

-- A substitution is a map from variables to terms
type Subst = [(Var, Term)]

-- Apply a substitution to a term
subst :: Subst -> Term -> Term
subst s (V x) =
    case chase s (V x) of
      V y -> V y
      t -> subst s t
subst s (F sym ts) =
    F sym (map (subst s) ts)

-- A substitution may contain an equivalence class of variables.  The
-- chase function finds the canonical representitive of the
-- equivalence class.
chase :: Subst -> Term -> Term
chase s (V x) =
    case lookup x s of
      Nothing -> V x
      Just t -> chase s t
chase _ t = t

-- UNIFICATION

-- This is the entry point
unify :: Term -> Term -> [Subst]
unify t t' =
    unify0 t t' []

-- Chase variables to start unifying two terms
unify0 :: Term -> Term -> Subst -> [Subst]
unify0 t t' s =
    unify1 (chase s t) (chase s t') s

-- Unification by case analysis
unify1 :: Term -> Term -> Subst -> [Subst]
unify1 (V x) (V y) s            -- Unify two variables
    | x == y = [s]              -- Nothing to do
    | x < y = [(y, V x) : s]    -- Substitute larger variable
    | otherwise = [(x, V y) : s] -- in preference to a smaller one
unify1 (V x) t s
    | occurs x t = []           -- Fail when x is in t
    | otherwise = [(x, t) : s]
unify1 t t'@(V _) s =
    unify1 t' t s
-- Unify using the Diffie-Hellman equation.
-- To make unification tractable, one makes use of the equation
-- exp(exp(gen(), x), y) = exp(exp(gen(), y), x).
unify1 (F "exp" ts@[u, v]) (F "exp" ts'@[u', v']) s =
    unifyList ts ts' s ++     -- Ordinary unification
    -- Add an instances of the equation, and unify on both sides
    do
      s' <- unifyList ts left s
      unifyList ts' right s'
    where
      -- Generate a fresh variable by looking at the variables in use
      var = nextVar ([u, v,  u', v'] ++ terms s) -- Include  substitution
      var' = var + 1                -- Generate another variable
      left = [F "exp" [F "gen" [], V var], V var'] -- One side of equation
      right = [F "exp" [F "gen" [], V var'], V var] -- And the other
unify1 (F sym ts) (F sym' ts') s -- Unify ordinary compound terms
    | sym /= sym' = []           -- Fail on symbol clash
    | otherwise = unifyList ts ts' s

unifyList :: [Term] -> [Term] -> Subst -> [Subst]
unifyList [] [] s = [s]
unifyList (t:ts) (t':ts') s =
    do
      s <- unify0 t t' s
      unifyList ts ts' s
unifyList _ _ _ = []

-- Find next unused variable in a list of terms
nextVar :: [Term] -> Var
nextVar [] = 0
nextVar ts =
    maximum (map nextVariable ts)
    where
      nextVariable (V x) = x + 1
      nextVariable (F _ ts) = nextVar ts

-- Returns the terms in a substitution.
terms :: Subst -> [Term]
terms s =
    [ t' |
      (x, t) <- s,
      t' <- [V x, t] ]

-- Does variable x occur in term t?
occurs :: Var -> Term -> Bool
occurs x (V y) = x == y
occurs x (F _ ts) = any (occurs x) ts

-- MATCHING

-- This is the entry point
match :: Term -> Term -> [Subst]
match t t' =
    match0 t t' []

-- Matching by case analysis
match0 :: Term -> Term -> Subst -> [Subst]
match0 (V x) t s =
    case lookup x s of
      Nothing -> [(x, t) : s]
      Just t' -> if t == t' then [s] else []
-- Match using the Diffie-Hellman equation
match0 (F "exp" [x, y]) (F "exp" [F "exp" [x', y'], z']) s =
    matchList [x, y] [F "exp" [x', y'], z'] s ++
    matchList [x, y] [F "exp" [x', z'], y'] s
match0 (F sym ts) (F sym' ts') s
    | sym /= sym' = []
    | otherwise = matchList ts ts' s
match0 _ _ _ = []

matchList :: [Term] -> [Term] -> Subst -> [Subst]
matchList [] [] s = [s]
matchList (t:ts) (t':ts') s =
    do
      s <- match0 t t' s
      matchList ts ts' s
matchList _ _ _ = []

-- TERM ORDERING

instance Ord Term where
    compare (V x) (V y) = compare x y
    compare (F "exp" [F "exp" [x, y], z])
            (F "exp" [F "exp" [x', y'], z']) =
        case (compare y z, compare y' z') of
          (GT, GT) -> compare [F "exp" [x, z], y] [F "exp" [x', z'], y']
          (GT, _) -> compare [F "exp" [x, z], y] [F "exp" [x', y'], z']
          (_, GT) -> compare [F "exp" [x, y], z] [F "exp" [x', z'], y']
          _ -> compare [F "exp" [x, y], z] [F "exp" [x', y'], z']
    compare (F sym ts) (F sym' ts') =
        case compare sym sym' of
          EQ -> compare ts ts'
          c -> c
    compare (V _) (F _ _) = LT
    compare (F _ _) (V _) = GT

-- TERM INPUT

instance Read Term where
    readsPrec _ s =
        readTerm s
        where
          readTerm s =
              [(V $ read (c:cs), t) | (c:cs, t) <- lex s,
                                      isDigit c] ++
              [(F (c:cs) ts, v)     | (c:cs, t) <- lex s,
                                      isAlpha c,
                                      ("(", u) <- lex t,
                                      (ts, v) <- readArgs u]
          readArgs s =
              [([], t)              | (")", t) <- lex s] ++
              [(x:xs, u)            | (x, t) <- reads s,
                                      (xs, u) <- readRest t]
          readRest s =
              [([], t)              | (")", t) <- lex s] ++
              [(x:xs, v)            | (",", t) <- lex s,
                                      (x, u) <- reads t,
                                      (xs, v) <- readRest u]

-- TERM OUTPUT

instance Show Term where
    showsPrec _ (V x) =
        shows x
    showsPrec _ (F sym ts) =
        showString sym . showChar '(' . showArgs ts
        where
          showArgs [] = showChar ')'
          showArgs (x:xs) = shows x . showRest xs
          showRest [] = showChar ')'
          showRest (x:xs) = showChar ',' . shows x . showRest xs
