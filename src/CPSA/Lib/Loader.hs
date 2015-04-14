-- Loads protocols and preskeletons from S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Loader (loadSExprs) where

import Control.Monad
import qualified Data.List as L
import Data.Maybe (isJust)
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal
import CPSA.Lib.Strand
import CPSA.Lib.Characteristic

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

-- Load protocols and preskeletons from a list of S-expressions, and
-- then return a list of preskeletons.  The name of the algebra is
-- nom, and its variable generator is provided.

loadSExprs :: (Algebra t p g s e c, Monad m) => String -> g ->
              [SExpr Pos] -> m [Preskel t g s e]
loadSExprs nom origin xs =
    do
      (_, ks) <- foldM (loadSExpr nom origin) ([], []) xs
      return (reverse ks)

loadSExpr :: (Algebra t p g s e c, Monad m) => String -> g ->
             ([Prot t g], [Preskel t g s e]) -> SExpr Pos ->
             m ([Prot t g], [Preskel t g s e])
loadSExpr nom origin (ps, ks) (L pos (S _ "defprotocol" : xs)) =
    do
      p <- loadProt nom origin pos xs
      return (p : ps, ks)
loadSExpr _ _ (ps, ks) (L pos (S _ "defskeleton" : xs)) =
    do
      k <- findPreskel pos ps xs
      return (ps, k : ks)
loadSExpr _ _ (ps, ks) (L pos (S _ "defgoal" : xs)) =
    do
      k <- findGoal pos ps xs
      return (ps, k : ks)
loadSExpr nom origin (ps, ks) (L pos (S pos' "defpreskeleton" : xs)) =
    loadSExpr nom origin (ps, ks) (L pos (S pos' "defskeleton" : xs))
loadSExpr _ _ (ps, ks) (L _ (S _ "comment" : _)) = return (ps, ks)
loadSExpr _ _ (ps, ks) (L _ (S _ "herald" : _)) = return (ps, ks)
loadSExpr _ _ _ x = fail (shows (annotation x) "Malformed input")

-- load a protocol

loadProt :: (Algebra t p g s e c, Monad m) => String -> g ->
            Pos -> [SExpr Pos] -> m (Prot t g)
loadProt nom origin pos (S _ name : S _ alg : x : xs)
    | alg /= nom =
        fail (shows pos $ "Expecting terms in algebra " ++ nom)
    | otherwise =
        do
          (gen, rs, comment) <- loadRoles origin (x : xs)
          -- Check for duplicate role names
          (gen, r) <- mkListenerRole pos gen
          validate (mkProt name alg gen rs r comment) rs
    where
      validate prot [] = return prot
      validate prot (r : rs) =
          case L.find (\r' -> rname r == rname r') rs of
            Nothing -> validate prot rs
            Just _ ->
                let msg = "Duplicate role " ++ rname r ++
                          " in protocol " ++ name in
                fail (shows pos msg)
loadProt _ _ pos _ = fail (shows pos "Malformed protocol")

loadRoles :: (Algebra t p g s e c, Monad m) => g -> [SExpr Pos] ->
             m (g, [Role t], [SExpr ()])
loadRoles gen (L pos (S _ "defrole" : x) : xs) =
    do
      (gen, r) <- loadRole gen pos x
      (gen, rs, comment) <- loadRoles gen xs
      return (gen, r : rs, comment)
loadRoles gen xs =
    do
      comment <- alist [] xs    -- Ensure remaining is an alist
      return (gen, [], comment)

loadRole :: (Algebra t p g s e c, Monad m) => g -> Pos ->
            [SExpr Pos] -> m (g, Role t)
loadRole gen pos (S _ name :
	          L _ (S _ "vars" : vars) :
                  L _ (S _ "trace" : evt : c) :
                  rest) =
    do
      (gen, vars) <- loadVars gen vars
      c <- loadTrace vars (evt : c)
      n <- loadPosBaseTerms vars (assoc "non-orig" rest)
      a <- loadPosBaseTerms vars (assoc "pen-non-orig" rest)
      u <- loadBaseTerms vars (assoc "uniq-orig" rest)
      comment <- alist ["non-orig", "pen-non-orig", "uniq-orig"] rest
      let reverseSearch = hasKey "reverse-search" rest
      let ts = tterms c
      case termsWellFormed (map snd n ++ map snd a ++ u ++ ts) of
        False -> fail (shows pos "Terms in role not well formed")
        True -> return ()
      -- Drop unused variable declarations
      let vs = L.filter (\v->elem v (varsInTerms ts)) vars
      -- Drop rnons that refer to unused variable declarations
      let ns = L.filter (varsSeen vs . snd) n
      -- Drop rpnons that refer to unused variable declarations
      let as = L.filter (varsSeen vs . snd) a
      -- Drop runiques that refer to unused variable declarations
      let us = L.filter (varsSeen vs) u
      prios <- mapM (loadRolePriority (length c)) (assoc "priority" rest)
      let r = mkRole name vs c ns as us comment prios reverseSearch
      case roleWellFormed r of
        Right () -> return (gen, r)
        Left msg -> fail (shows pos $ showString "Role not well formed: " msg)
loadRole _ pos _ = fail (shows pos "Malformed role")

loadRolePriority :: Monad m => Int -> SExpr Pos -> m (Int, Int)
loadRolePriority n (L _ [N _ i, N _ p])
    | 0 <= i && i < n = return (i, p)
loadRolePriority _ x = fail (shows (annotation x) "Malformed priority")

-- Are the vars in t a subset of ones in t.
varsSeen :: Algebra t p g s e c => [t] -> t -> Bool
varsSeen vs t =
    all (flip elem vs) (addVars [] t)

-- A role is well formed if all non-base variables are receive bound,
-- each atom declared to be uniquely-originating originates in
-- the trace, and every variable that occurs in each atom
-- declared to be non-originating occurs in some term in the trace,
-- and the atom must never be carried by any term in the trace.
roleWellFormed :: (Monad m, Algebra t p g s e c) => Role t -> m ()
roleWellFormed role =
    do
      failwith "a variable in non-orig is not in trace"
                   $ varSubset (map snd $ rnon role) terms
      failwith "a variable in pen-non-orig is not in trace"
                   $ varSubset (map snd $ rpnon role) terms
      mapM_ nonCheck $ rnon role
      mapM_ lenCheck $ rnon role
      mapM_ lenCheck $ rpnon role
      mapM_ uniqueCheck $ runique role
      mapM_ origVarCheck $ rvars role
      failwith "role trace is a prefix of a listener"
                   $ notListenerPrefix $ rtrace role
    where
      terms = tterms (rtrace role)
      nonCheck (_, t) =
          failwith (showString "non-orig " $ showst t " carried")
                       $ all (not . carriedBy t) terms
      lenCheck (Nothing, _) = return ()
      lenCheck (Just len, _) | len >= length (rtrace role) =
          fail $ showString "invalid position " $ show len
      lenCheck (Just len, t) | otherwise =
          case usedPos t (rtrace role) of
            Just p | p <= len -> return ()
            Just _ -> fail $ showst t
                      $ showString " appears after position " $ show len
            Nothing -> fail msg
          where
            msg = "no used position for non-originating atom " ++ showst t ""
      uniqueCheck t =
          failwith (showString "uniq-orig " $ showst  t " doesn't originate")
                       $ originates t (rtrace role)
      origVarCheck v =
          failwith (showString "variable " $ showst v " not acquired")
                       $ not (isAcquiredVar v) ||
                         isJust (acquiredPos v (rtrace role))

failwith :: Monad m => String -> Bool -> m ()
failwith msg test =
    case test of
      True -> return ()
      False -> fail msg

showst :: Algebra t p g s e c => t -> ShowS
showst t =
    shows $ displayTerm (addToContext emptyContext [t]) t

-- This is the only place a role is generated with an empty name.
-- This is what marks a strand as a listener.
mkListenerRole :: (Algebra t p g s e c, Monad m) => Pos -> g -> m (g, Role t)
mkListenerRole pos g =
  do
    (g, [x]) <- loadVars g [L pos [S pos "x", S pos "mesg"]]
    return (g, mkRole "" [x] [In x, Out x] [] [] [] [] [] False)

-- Ensure a trace is not a prefix of a listener
notListenerPrefix :: Algebra t p g s e c => Trace t -> Bool
notListenerPrefix (In t : Out t' : _) | t == t' = False
notListenerPrefix _ = True

-- Association lists

-- Make an association list into a comment.  The first argument is the
-- set of keys of key-value pairs to be dropped from the comment.

alist :: Monad m => [String] -> [SExpr Pos] -> m [SExpr ()]
alist _ [] = return []
alist keys (a@(L _ (S _ key : _)) : xs)
    | elem key keys = alist keys xs
    | otherwise =
        do
          xs <- alist keys xs
          return $ strip a : xs
alist _ xs = fail (shows (annotation $ head xs) "Malformed association list")

-- Strip positions from an S-expression

strip :: SExpr a -> SExpr ()
strip (S _ s) = S () s
strip (Q _ s) = Q () s
strip (N _ n) = N () n
strip (L _ l) = L () (map strip l)

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr a] -> [SExpr a]
assoc key alist =
    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]

-- See if alist has a key
hasKey :: String -> [SExpr a] -> Bool
hasKey key alist =
    any f alist
    where
      f (L _ (S _ head : _)) = head == key
      f _ = False

loadTrace :: (Algebra t p g s e c, Monad m) => [t] ->
             [SExpr Pos] -> m (Trace t)
loadTrace vars xs = mapM (loadEvt vars) xs

loadEvt :: (Algebra t p g s e c, Monad m) => [t] ->
          SExpr Pos -> m (Event t)
loadEvt vars (L _ [S _ "recv", t]) =
    do
      t <- loadTerm vars t
      return (In t)
loadEvt vars (L _ [S _ "send", t]) =
    do
      t <- loadTerm vars t
      return (Out t)
loadEvt _ (L pos [S _ dir, _]) =
    fail (shows pos $ "Unrecognized direction " ++ dir)
loadEvt _ x = fail (shows (annotation x) "Malformed direction")

loadBaseTerms :: (Algebra t p g s e c, Monad m) => [t] -> [SExpr Pos] -> m [t]
loadBaseTerms _ [] = return []
loadBaseTerms vars (x : xs) =
    do
      t <- loadBaseTerm vars x
      ts <- loadBaseTerms vars xs
      return (adjoin t ts)

loadBaseTerm :: (Algebra t p g s e c, Monad m) => [t] -> SExpr Pos -> m t
loadBaseTerm vars x =
    do
      t <- loadTerm vars x
      case isAtom t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an atom")

loadPosBaseTerms :: (Algebra t p g s e c, Monad m) => [t] ->
                    [SExpr Pos] -> m [(Maybe Int, t)]
loadPosBaseTerms _ [] = return []
loadPosBaseTerms vars (x : xs) =
    do
      t <- loadPosBaseTerm vars x
      ts <- loadPosBaseTerms vars xs
      return (t:ts)

loadPosBaseTerm :: (Algebra t p g s e c, Monad m) => [t] ->
                   SExpr Pos -> m (Maybe Int, t)
loadPosBaseTerm vars x'@(L _ [N _ opos, x])
    | opos < 0 =
        fail (shows (annotation x')
              "Expecting a non-negative non-origination position")
    | otherwise =
        do
          t <- loadBaseTerm vars x
          return (Just opos, t)
loadPosBaseTerm vars x =
    do
      t <- loadTerm vars x
      case isAtom t of
        True -> return (Nothing, t)
        False -> fail (shows (annotation x) "Expecting an atom")

-- Find protocol and then load a preskeleton.

findPreskel :: (Algebra t p g s e c, Monad m) => Pos ->
               [Prot t g] -> [SExpr Pos] ->
               m (Preskel t g s e)
findPreskel pos ps (S _ name : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> loadPreskel pos p xs
findPreskel pos _ _ = fail (shows pos "Malformed skeleton")

loadPreskel :: (Algebra t p g s e c, Monad m) => Pos ->
               Prot t g -> [SExpr Pos] ->
               m (Preskel t g s e)
loadPreskel pos p (L _ (S _ "vars" : vars) : xs) =
    do
      (gen, kvars) <- loadVars (pgen p) vars
      loadInsts pos p kvars gen [] xs
loadPreskel pos _ _ = fail (shows pos "Malformed skeleton")

loadInsts :: (Algebra t p g s e c, Monad m) => Pos ->
             Prot t g -> [t] -> g -> [Instance t e] ->
             [SExpr Pos] -> m (Preskel t g s e)
loadInsts top p kvars gen insts (L pos (S _ "defstrand" : x) : xs) =
    case x of
      S _ role : N _ height : env ->
          do
            (gen, i) <- loadInst pos p kvars gen role height env
            loadInsts top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrand")
loadInsts top p kvars gen insts (L pos (S _ "deflistener" : x) : xs) =
    case x of
      [term] ->
          do
            (gen, i) <- loadListener p kvars gen term
            loadInsts top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed deflistener")
loadInsts top p kvars gen insts xs =
    do
      _ <- alist [] xs          -- Check syntax of xs
      (gen, gs) <- loadGoals top p gen goals
      loadRest top kvars p gen gs (reverse insts) order nr ar ur pl kcomment
    where
      order = assoc "precedes" xs
      nr = assoc "non-orig" xs
      ar = assoc "pen-non-orig" xs
      ur = assoc "uniq-orig" xs
      pl = assoc "priority" xs
      goals = assoc "goals" xs
      kcomment =
        loadComment "goals" goals ++
        loadComment "comment" (assoc "comment" xs)

loadComment :: String -> [SExpr Pos] -> [SExpr ()]
loadComment _ [] = []
loadComment key comment =
  [L () (S () key : map strip comment)]

loadInst :: (Algebra t p g s e c, Monad m) => Pos ->
            Prot t g -> [t] -> g -> String -> Int ->
            [SExpr Pos] -> m (g, Instance t e)
loadInst pos p kvars gen role height env =
    do
      r <- lookupRole pos p role
      case height < 1 || height > length (rtrace r) of
        True -> fail (shows pos "Bad height")
        False ->
            do
              let vars = rvars r
              (gen', env') <- foldM (loadMaplet kvars vars) (gen, emptyEnv) env
              return (mkInstance gen' r env' height)

lookupRole :: (Algebra t p g s e c, Monad m) => Pos ->
              Prot t g -> String -> m (Role t)
lookupRole _ p role  | role == "" =
    return $ listenerRole p
lookupRole pos p role =
    case L.find (\r -> role == rname r) (roles p) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname p)
      Just r -> return r

loadMaplet :: (Algebra t p g s e c, Monad m) => [t] -> [t] ->
              (g, e) -> SExpr Pos -> m (g, e)
loadMaplet kvars vars env (L pos [domain, range]) =
    do
      t <- loadTerm vars domain
      t' <- loadTerm kvars range
      case match t t' env of
        env' : _ -> return env'
        [] -> fail (shows pos "Domain does not match range")
loadMaplet _ _ _ x = fail (shows (annotation x) "Malformed maplet")

loadListener :: (Algebra t p g s e c, Monad m) => Prot t g ->
                [t] -> g -> SExpr Pos -> m (g, Instance t e)
loadListener p kvars gen x =
    do
     t <- loadTerm kvars x
     return $ mkListener p gen t

loadRest :: (Algebra t p g s e c, Monad m) => Pos -> [t] ->
            Prot t g -> g -> [Goal t] -> [Instance t e] ->
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr Pos] -> [SExpr ()] -> m (Preskel t g s e)
loadRest pos vars p gen gs insts orderings nr ar ur pl comment =
    do
      case null insts of
        True -> fail (shows pos "No strands")
        False -> return ()
      let heights = map height insts
      o <- loadOrderings heights orderings
      nr <- loadBaseTerms vars nr
      ar <- loadBaseTerms vars ar
      ur <- loadBaseTerms vars ur
      let (nr', ar', ur') = foldl addInstOrigs (nr, ar, ur) insts
      prios <- mapM (loadPriorities heights) pl
      let k = mkPreskel gen p gs insts o nr' ar' ur' prios comment
      case termsWellFormed $ nr' ++ ar' ++ ur' ++ kterms k of
        False -> fail (shows pos "Terms in skeleton not well formed")
        True -> return ()
      case verbosePreskelWellFormed k of
        Right () -> return k
        Left msg -> fail $ shows pos
                    $ showString "Skeleton not well formed: " msg

loadOrderings :: Monad m => [Int] -> [SExpr Pos] -> m [Pair]
loadOrderings heights x =
    foldM f [] x
    where
      f ns x =
          do
            np <- loadPair heights x
            return (adjoin np ns)

loadPair :: Monad m => [Int] -> SExpr Pos -> m Pair
loadPair heights (L pos [x0, x1]) =
    do
      n0 <- loadNode heights x0
      n1 <- loadNode heights x1
      case sameStrands n0 n1 of  -- Same strand
        True -> fail (shows pos "Malformed pair -- nodes in same strand")
        False -> return (n0, n1)
    where
      sameStrands (s0, _) (s1, _) = s0 == s1
loadPair _ x = fail (shows (annotation x) "Malformed pair")

loadNode :: Monad m => [Int] -> SExpr Pos -> m Node
loadNode heights (L pos [N _ s, N _ p])
    | s < 0 = fail (shows pos "Negative strand in node")
    | p < 0 = fail (shows pos "Negative position in node")
    | otherwise =
        case height heights s of
          Nothing -> fail (shows pos "Bad strand in node")
          Just h | p < h -> return (s, p)
          _ -> fail (shows pos "Bad position in node")
    where
      height [] _ = Nothing
      height (x: xs) s          -- Assume s non-negative
          | s == 0 = Just x
          | otherwise = height xs (s - 1)
loadNode _ x = fail (shows (annotation x) "Malformed node")

loadPriorities :: Monad m => [Int] -> SExpr Pos -> m (Node, Int)
loadPriorities heights (L _ [x, N _ p]) =
    do
      n <- loadNode heights x
      return (n, p)
loadPriorities _ x =
    fail (shows (annotation x) "Malformed priority")

addInstOrigs :: Algebra t p g s e c => ([t], [t], [t]) ->
                Instance t e -> ([t], [t], [t])
addInstOrigs (nr, ar, ur) i =
    (foldl (flip adjoin) nr $ inheritRnon i,
     foldl (flip adjoin) ar $ inheritRpnon i,
     foldl (flip adjoin) ur $ inheritRunique i)

-- Security goals

-- Load a defgoal form
findGoal :: (Algebra t p g s e c, Monad m) => Pos ->
            [Prot t g] -> [SExpr Pos] -> m (Preskel t g s e)
findGoal pos ps (S _ name : x : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p ->
        do
          (g, goal, antec) <- loadSentence pos p (pgen p) x
          let (gs, xs') = findAlist xs
          (g, goals) <- loadGoals pos p g gs
          _ <- alist [] xs'          -- Check syntax of xs
          let kcomment =
                loadComment "goals" (x : gs) ++
                loadComment "comment" (assoc "comment" xs')
          -- Make and return the characteristic skeleton of a security goal
          characteristic pos p (goal : goals) g antec kcomment
findGoal pos _ _ = fail (shows pos "Malformed goal")

-- Separate argument into goals and any remaining elements of an
-- association list.
findAlist :: [SExpr Pos] -> ([SExpr Pos], [SExpr Pos])
findAlist [] = ([], [])
findAlist (x@(L _ (S _ "forall" : _)) : xs) =
  (x : gs, xs')
  where
    (gs, xs') = findAlist xs
findAlist xs = ([], xs)

--- Load a sequence of security goals

loadGoals :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
             g -> [SExpr Pos] -> m (g, [Goal t])
loadGoals _ _ g [] = return (g, [])
loadGoals pos prot g (x : xs) =
  do
    (g, goal, _) <- loadSentence pos prot g x
    (g, goals) <- loadGoals pos prot g xs
    return (g, goal : goals)

-- Load a single security goal, a universally quantified formula
-- Returns the goal and the antecedent with position information.

loadSentence :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                g -> SExpr Pos -> m (g, Goal t, Conj t)
loadSentence _ prot g (L pos [S _ "forall", L _ vs, x]) =
  do
    (g, vars) <- loadVars g vs
    loadImplication pos prot g (L.nub $ reverse vars) x
loadSentence pos _ _ _ = fail (shows pos "Bad goal sentence")

-- Load the top-level implication of a security goal

loadImplication :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                   g -> [t] -> SExpr Pos -> m (g, Goal t, Conj t)
loadImplication _ prot g vars (L pos [S _ "implies", a, c]) =
  do
    (g, antec) <- loadRoleSpecific pos prot g vars vars a
    (g, concl) <- loadConclusion pos prot g vars c
    let goal =
          Goal { uvars = vars,
                 antec = map snd antec,
                 concl = map (map snd) concl }
    return (g, goal, antec)
loadImplication pos _ _ _ _ = fail (shows pos "Bad goal implication")

-- The conclusion must be a disjunction.  Each disjunct may introduce
-- existentially quantified variables.

loadConclusion :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                  g -> [t] -> SExpr Pos -> m (g, [Conj t])
loadConclusion _ _ g _ (L _ [S _ "false"]) = return (g, [])
loadConclusion _ prot g vars (L pos (S _ "or" : xs)) =
  loadDisjuncts pos prot g vars xs []
loadConclusion pos prot g vars x =
  do
    (g, a) <- loadExistential pos prot g vars x
    return (g, [a])

loadDisjuncts :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                 g -> [t] -> [SExpr Pos] -> [Conj t] -> m (g, [Conj t])
loadDisjuncts _ _ g _ [] rest = return (g, reverse rest)
loadDisjuncts pos prot g vars (x : xs) rest =
  do
    (g, a) <- loadExistential pos prot g vars x
    loadDisjuncts pos prot g vars xs (a : rest)

loadExistential :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                   g -> [t] -> SExpr Pos -> m (g, Conj t)
loadExistential _ prot g vars (L pos [S _ "exists", L _ vs, x]) =
  do
    (g, evars) <- loadVars g vs
    loadRoleSpecific pos prot g (reverse evars ++ vars) evars x
loadExistential pos prot g vars x =
  loadRoleSpecific pos prot g vars [] x

--- Load a conjunction of atomic formulas and ensure the formula is
--- role specific.

loadRoleSpecific :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                    g -> [t] -> [t] -> SExpr Pos -> m (g, Conj t)
loadRoleSpecific pos prot g vars unbound x =
  do
    (g, as) <- loadConjunction pos prot vars g x
    let as' = L.sortBy (\(_, x) (_, y) -> aFormOrder x y) as
    unbound <- foldM roleSpecific unbound as'
    case unbound of
      [] -> return (g, as')
      (v : _) -> fail (shows (annotation x) (showst v " not used"))

-- Load a conjunction of atomic formulas

loadConjunction :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                   [t] -> g -> SExpr Pos -> m (g, Conj t)
loadConjunction _ p kvars g (L pos (S _ "and" : xs)) =
  loadConjuncts pos p kvars g xs []
loadConjunction top p kvars g x =
  do
    (g, pos, a) <- loadPrimary top p kvars g x
    return (g, [(pos, a)])

loadConjuncts :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                 [t] -> g -> [SExpr Pos] -> Conj t -> m (g, Conj t)
loadConjuncts _ _ _ g [] rest = return (g, reverse rest)
loadConjuncts top p kvars g (x : xs) rest =
  do
    (g, pos, a) <- loadPrimary top p kvars g x
    loadConjuncts top p kvars g xs ((pos, a) : rest)

-- Load the atomic formulas

loadPrimary :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
               [t] -> g -> SExpr Pos -> m (g, Pos, AForm t)
loadPrimary _ _ kvars g (L pos [S _ "=", x, y]) =
  do
    (g, t) <- loadSgTerm kvars g x
    (g, t') <- loadSgTerm kvars g y
    return (g, pos, Equals t t')
loadPrimary _ _ kvars g (L pos [S _ "non", x]) =
  do
    t <- loadAlgTerm kvars x
    return (g, pos, Non t)
loadPrimary _ _ kvars g (L pos [S _ "pnon", x]) =
  do
    t <- loadAlgTerm kvars x
    return (g, pos, Pnon t)
loadPrimary _ _ kvars g (L pos [S _ "uniq", x]) =
  do
    t <- loadAlgTerm kvars x
    return (g, pos, Uniq t)
loadPrimary _ _ kvars g (L pos [S _ "uniq-at", x, y]) =
  do
    t <- loadAlgTerm kvars x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, UniqAt t t')
loadPrimary _ _ kvars g (L pos [S _ "str-prec", x, y]) =
  do
    (g, t) <- loadNodeTerm kvars g x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, StrPrec t t')
loadPrimary _ _ kvars g (L pos [S _ "prec", x, y]) =
  do
    (g, t) <- loadNodeTerm kvars g x
    (g, t') <- loadNodeTerm kvars g y
    return (g, pos, Prec t t')
loadPrimary _ p kvars g (L pos [S _ "p", Q _ name, N _ i, x]) =
  do
    r <- lookupRole pos p name
    (g, t) <- loadNodeTerm kvars g x
    case i < 0 || i >= length (rtrace r) of
      True -> fail (shows pos "Bad index")
      False -> return (g, pos, RolePred r i t)
loadPrimary _ p kvars g (L pos [S _ "p", Q _ name, Q var x, y, z]) =
  do
    r <- lookupRole pos p name
    v <- loadAlgTerm (rvars r) (S var x)
    (g, n) <- loadNodeTerm kvars g y
    t <- loadAlgTerm kvars z
    case isVar v of
      False -> fail (shows pos "Bad parameter -- not a variable")
      True -> return (g, pos, ParamPred r v n t)
loadPrimary _ _ _ _ (L pos (S _ "p" : Q _ name : _)) =
  fail (shows pos ("Bad role specific formula for role " ++ name))
loadPrimary _ _ _ _ (L pos (S _ pred : _)) =
  fail (shows pos ("Bad formula for predicate " ++ pred))
loadPrimary pos _ _ _ _ = fail (shows pos "Bad formula")

-- Load a term and make sure it has sort node

loadNodeTerm :: (Algebra t p g s e c, Monad m) => [t] -> g ->
                SExpr Pos -> m (g, t)
loadNodeTerm ts g x =
  do
    (g, t) <- loadSgTerm ts g x
    case isNodeVar t of
      True -> return (g, t)
      False -> fail (shows (annotation x) "Expecting a node variable")

-- Load a term and make sure it does not have sort node

loadAlgTerm :: (Algebra t p g s e c, Monad m) => [t] -> SExpr Pos -> m t
loadAlgTerm _ x@(L _ [N _ _, N _ _]) =
  fail (shows (annotation x) "Expecting an algebra term")
loadAlgTerm ts x =
  do
    t <- loadTerm ts x
    case isNodeVar t of
      True -> fail (shows (annotation x) "Expecting an algebra term")
      False -> return t

loadSgTerm :: (Algebra t p g s e c, Monad m) => [t] -> g ->
              SExpr Pos -> m (g, t)
loadSgTerm ts g x =
  do
    t <- loadTerm ts x
    return (g, t)

-- Role specific check

termVars :: Algebra t p g s e c => t -> [t]
termVars t = addVars [] t

allBound :: Algebra t p g s e c => [t] -> t -> Bool
allBound unbound t =
  L.all (flip L.notElem unbound) (termVars t)

-- Returns variables in unbound that are not role specific

roleSpecific :: (Algebra t p g s e c, Monad m) =>
                [t] -> (Pos, AForm t) -> m [t]
roleSpecific unbound (_, RolePred _ _ n) =
  return $ L.delete n unbound
roleSpecific unbound (pos, ParamPred _ _ n t)
  | L.notElem n unbound = return $ unbound L.\\ termVars t
  | otherwise = fail (shows pos "Unbound variable in parameter predicate")
roleSpecific unbound (pos, StrPrec n n')
  | L.notElem n unbound && L.notElem n' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in str-prec")
roleSpecific unbound (pos, Prec n n')
  | L.notElem n unbound && L.notElem n' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in prec")
roleSpecific unbound (pos, Non t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in non")
roleSpecific unbound (pos, Pnon t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in pnon")
roleSpecific unbound (pos, Uniq t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in uniq")
roleSpecific unbound (pos, UniqAt t n)
  | allBound unbound t && L.notElem n unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in uniq-at")
roleSpecific unbound (pos, Equals t t')
  | isNodeVar t && isNodeVar t' =
    case L.notElem t unbound && L.notElem t' unbound of
      True -> return unbound
      False -> fail (shows pos "Unbound variable in equals")
  | isNodeVar t = fail (shows pos "Type mismatch in equals")
  | isNodeVar t' = fail (shows pos "Type mismatch in equals")
  | allBound unbound t && allBound unbound t' = return unbound
  | otherwise = fail (shows pos "Unbound variable in equals")
