-- Loads protocols and preskeletons from S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Loader (loadSExprs) where

import Control.Monad
import Control.Applicative ()
import qualified Data.List as L
import Data.Maybe (isJust)
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Protocol
import CPSA.Strand
import CPSA.Characteristic

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

-- Load protocols and preskeletons from a list of S-expressions, and
-- then return a list of preskeletons.  The name of the algebra is
-- nom, and its variable generator is provided.

loadSExprs :: Monad m => String -> Gen -> [SExpr Pos] -> m [Preskel]
loadSExprs nom origin xs =
    do
      (_, ks) <- foldM (loadSExpr nom origin) ([], []) xs
      return (reverse ks)

loadSExpr :: Monad m => String -> Gen -> ([Prot], [Preskel]) ->
             SExpr Pos -> m ([Prot], [Preskel])
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

loadProt :: Monad m => String -> Gen -> Pos -> [SExpr Pos] -> m Prot
loadProt nom origin pos (S _ name : S _ alg : x : xs)
    | alg /= nom =
        fail (shows pos $ "Expecting terms in algebra " ++ nom)
    | otherwise =
        do
          (gen, rs, rest) <- loadRoles origin (x : xs)
          (gen, r) <- mkListenerRole pos gen
          -- Check for duplicate role names
          (rules, comment) <- loadRules rs rest
          validate (mkProt name alg gen rs r rules comment) rs
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

loadRoles :: Monad m => Gen -> [SExpr Pos] -> m (Gen, [Role], [SExpr Pos])
loadRoles gen (L pos (S _ "defrole" : x) : xs) =
    do
      (gen, r) <- loadRole gen pos x
      (gen, rs, comment) <- loadRoles gen xs
      return (gen, r : rs, comment)
loadRoles gen comment =
    return (gen, [], comment)

loadRole :: Monad m => Gen -> Pos -> [SExpr Pos] -> m (Gen, Role)
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
        Return () -> return (gen, r)
        Fail msg -> fail (shows pos $ showString "Role not well formed: " msg)
loadRole _ pos _ = fail (shows pos "Malformed role")

-- Like Either String but with fail method defined
data ReturnFail a
    = Return a
    | Fail String

instance Functor ReturnFail where
    fmap _ (Fail x)   = Fail x
    fmap f (Return y) = Return (f y)

instance Applicative ReturnFail where
    pure           = Return
    Fail e <*> _   = Fail e
    Return f <*> r = fmap f r

instance Monad ReturnFail where
    Fail l >>= _   = Fail l
    Return r >>= k = k r
    fail s         = Fail s     -- This must be removed eventually

loadRolePriority :: Monad m => Int -> SExpr Pos -> m (Int, Int)
loadRolePriority n (L _ [N _ i, N _ p])
    | 0 <= i && i < n = return (i, p)
loadRolePriority _ x = fail (shows (annotation x) "Malformed priority")

-- Are the vars in t a subset of ones in t.
varsSeen :: [Term] -> Term -> Bool
varsSeen vs t =
    all (flip elem vs) (addVars [] t)

-- A role is well formed if all non-base variables are receive bound,
-- each atom declared to be uniquely-originating originates in
-- the trace, and every variable that occurs in each atom
-- declared to be non-originating occurs in some term in the trace,
-- and the atom must never be carried by any term in the trace.
roleWellFormed :: Monad m => Role -> m ()
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

showst :: Term -> ShowS
showst t =
    shows $ displayTerm (addToContext emptyContext [t]) t

-- This is the only place a role is generated with an empty name.
-- This is what marks a strand as a listener.
mkListenerRole :: Monad m => Pos -> Gen -> m (Gen, Role)
mkListenerRole pos g =
  do
    (g, xs) <- loadVars g [L pos [S pos "x", S pos "mesg"]]
    case xs of
      [x] -> return (g, mkRole "" [x] [In x, Out x] [] [] [] [] [] False)
      _ -> fail "mkListenerRole: expecting one variable"

-- Ensure a trace is not a prefix of a listener
notListenerPrefix :: Trace -> Bool
notListenerPrefix (In t : Out t' : _) | t == t' = False
notListenerPrefix _ = True

-- Protocol Rules

loadRules :: Monad m => [Role] -> [SExpr Pos] -> m ([Rule], [SExpr ()])
loadRules rs (L pos (S _ "defrule" : x) : xs) =
    do
      r <- loadRule rs pos x
      (rs, comment) <- loadRules rs xs
      return (r : rs, comment)
loadRules _ xs =
    do
      comment <- alist [] xs    -- Ensure remaining is an alist
      return ([], comment)

loadRule :: Monad m => [Role] -> Pos -> [SExpr Pos] -> m Rule
loadRule rs pos (S _ name : xs) =
  loadUImplies rs pos name xs
loadRule _ pos _ =
  fail (shows pos "Malformed rule")

loadUImplies :: Monad m => [Role] -> Pos -> String ->
                [SExpr Pos] -> m Rule
loadUImplies rs _ name (L _ [S _ "implies", antec, concl] : cmt) =
  do
    antec <- loadUConj rs name antec
    concl <- loadUDisj rs name concl
    return $ Rule { uname = name,
                    uantec = antec,
                    uconcl = concl,
                    ucomment = map strip cmt }
loadUImplies _ pos name _ =
  fail (shows pos ("In rule " ++ name ++ ", expecting implies"))

loadUDisj :: Monad m => [Role] -> String -> SExpr Pos -> m [[UForm]]
loadUDisj _ _ (L _ [S _ "false"]) =
  return []
loadUDisj rs name (L _ (S _ "or" : xs)) =
  mapM (loadUConj rs name) xs
loadUDisj rs name x =
  do
    conj <- loadUConj rs name x
    return [conj]

loadUConj :: Monad m => [Role] -> String -> SExpr Pos -> m [UForm]
loadUConj _ name (L pos [S _ "and"]) =
  fail (shows pos ("In rule " ++ name ++ ", malformed and"))
loadUConj rs name (L _ (S _ "and" : xs)) =
  mapM (loadUForm rs name) xs
loadUConj rs name x =
  do
    form <- loadUForm rs name x
    return [form]

loadUForm :: Monad m => [Role] -> String -> SExpr Pos -> m UForm
loadUForm rs _
  (L _ [S _ "p", Q pos r, S _ var, N _ n])
  | n > 0 =
    do
      r <- lookForRole rs name pos r
      return $ ULen r var n
loadUForm rs name
  (L _ [S _ "p", Q pos r, Q p var, S _ strd, t]) =
  do
    r <- lookForRole rs name pos r
    v <- loadAlgTerm (rvars r) (S p var)
    t <- loadUAlgTerm t
    case firstOccurs v r of
      Just i -> return (UParam r v (i + 1) strd t)
      Nothing -> fail (shows p ("Parameter " ++ var ++
                                " not in role " ++ rname r))
loadUForm _ _
  (L _ [S _ "prec", n1, n2]) =
  do
    n1 <- loadNodeUTerm n1
    n2 <- loadNodeUTerm n2
    return $ UPrec n1 n2
loadUForm _ _
  (L _ [S _ "non", t]) =
  do
    t <- loadUAlgTerm t
    return $ UNon t
loadUForm _ _
  (L _ [S _ "pnon", t]) =
  do
    t <- loadUAlgTerm t
    return $ UPnon t
loadUForm _ _
  (L _ [S _ "uniq", t]) =
  do
    t <- loadUAlgTerm t
    return $ UUniq t
loadUForm _ _
  (L _ (S _ "fact" : S _ name : fs)) =
  do
    fs <- mapM loadUTerm fs
    return $ UFact name fs
loadUForm _ _
  (L _ [S _ "=", t1, t2]) =
  do
    t1 <- loadUTerm t1
    t2 <- loadUTerm t2
    return $ UEquals t1 t2
loadUForm _ name (L pos (S _ "p" : Q _ r : Q _ var : _)) =
  fail (shows pos "In rule " ++ name ++
        ", malformed parameter predicate for role " ++ r ++
        " and parameter " ++ var) 
loadUForm _ name (L pos (S _ "p" : Q _ r : _)) =
  fail (shows pos "In rule " ++ name ++
        ", malformed role length predicate for role " ++ r)
loadUForm _ name (L pos (S _ pred : _)) =
  fail (shows pos "In rule " ++ name ++
        ", predicate " ++ pred ++ " unrecognized or formula malformed")
loadUForm _ name xs =
  fail (shows (annotation xs) "In rule " ++ name ++
        ", malformed formula")

lookForRole :: Monad m => [Role] -> String -> Pos -> String -> m Role
lookForRole rs name pos var =
  case L.find (\r -> var == rname r) rs of
    Just r -> return r
    Nothing ->
      fail (shows pos ("In rule " ++ name ++
                       ", role " ++ var ++ " not found"))

loadUTerm :: Monad m => SExpr Pos -> m UTerm
loadUTerm (S _ var) = return $ UVar var
loadUTerm (L _ [S _ var, N _ num])
  | num >= 0 = return $ UNode (var, num)
loadUTerm (L _ [S _ "invk", S _ var]) = return $ UInv var
loadUTerm (L pos (_ : N _ _ : _)) =
  fail (shows pos "Bad node term")
loadUTerm (L pos (S _ fun : _)) =
  fail (shows pos "Bad function application with " ++ fun)
loadUTerm x = fail (shows (annotation x) "Bad term")

loadUAlgTerm :: Monad m => SExpr Pos -> m UTerm
loadUAlgTerm x =
  do
    t <- loadUTerm x
    case t of
      UNode _ -> fail (shows (annotation x) "Not expecting a node")
      _ -> return t

loadNodeUTerm :: Monad m => SExpr Pos -> m NodeUTerm
loadNodeUTerm x =
  do
    t <- loadUTerm x
    case t of
      UNode n -> return n
      _ -> fail (shows (annotation x) "Expecting a node")

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

loadTrace :: Monad m => [Term] -> [SExpr Pos] -> m Trace
loadTrace vars xs = mapM (loadEvt vars) xs

loadEvt :: Monad m => [Term] -> SExpr Pos -> m Event
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
loadEvt _ x = fail (shows (annotation x) "Malformed event")

loadBaseTerms :: Monad m => [Term] -> [SExpr Pos] -> m [Term]
loadBaseTerms _ [] = return []
loadBaseTerms vars (x : xs) =
    do
      t <- loadBaseTerm vars x
      ts <- loadBaseTerms vars xs
      return (adjoin t ts)

loadBaseTerm :: Monad m => [Term] -> SExpr Pos -> m Term
loadBaseTerm vars x =
    do
      t <- loadTerm vars x
      case isAtom t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an atom")

loadPosBaseTerms :: Monad m => [Term] -> [SExpr Pos] -> m [(Maybe Int, Term)]
loadPosBaseTerms _ [] = return []
loadPosBaseTerms vars (x : xs) =
    do
      t <- loadPosBaseTerm vars x
      ts <- loadPosBaseTerms vars xs
      return (t:ts)

loadPosBaseTerm :: Monad m => [Term] -> SExpr Pos -> m (Maybe Int, Term)
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

findPreskel :: Monad m => Pos -> [Prot] -> [SExpr Pos] -> m Preskel
findPreskel pos ps (S _ name : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> loadPreskel pos p xs
findPreskel pos _ _ = fail (shows pos "Malformed skeleton")

loadPreskel :: Monad m => Pos -> Prot -> [SExpr Pos] -> m Preskel
loadPreskel pos p (L _ (S _ "vars" : vars) : xs) =
    do
      (gen, kvars) <- loadVars (pgen p) vars
      loadInsts pos p kvars gen [] xs
loadPreskel pos _ _ = fail (shows pos "Malformed skeleton")

loadInsts :: Monad m => Pos -> Prot -> [Term] -> Gen -> [Instance] ->
             [SExpr Pos] -> m Preskel
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
      loadRest top kvars p gen gs (reverse insts) order nr ar ur fs pl kcomment
    where
      order = assoc "precedes" xs
      nr = assoc "non-orig" xs
      ar = assoc "pen-non-orig" xs
      ur = assoc "uniq-orig" xs
      fs = assoc "facts" xs
      pl = assoc "priority" xs
      goals = assoc "goals" xs
      kcomment =
        loadComment "goals" goals ++
        loadComment "comment" (assoc "comment" xs)

loadComment :: String -> [SExpr Pos] -> [SExpr ()]
loadComment _ [] = []
loadComment key comment =
  [L () (S () key : map strip comment)]

loadInst :: Monad m => Pos -> Prot -> [Term] -> Gen -> String ->
            Int -> [SExpr Pos] -> m (Gen, Instance)
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

lookupRole :: Monad m => Pos -> Prot -> String -> m Role
lookupRole _ p role  | role == "" =
    return $ listenerRole p
lookupRole pos p role =
    case L.find (\r -> role == rname r) (roles p) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname p)
      Just r -> return r

loadMaplet :: Monad m => [Term] -> [Term] ->
              (Gen, Env) -> SExpr Pos -> m (Gen, Env)
loadMaplet kvars vars env (L pos [domain, range]) =
    do
      t <- loadTerm vars domain
      t' <- loadTerm kvars range
      case match t t' env of
        env' : _ -> return env'
        [] -> fail (shows pos "Domain does not match range")
loadMaplet _ _ _ x = fail (shows (annotation x) "Malformed maplet")

loadListener :: Monad m => Prot -> [Term] -> Gen -> SExpr Pos ->
                m (Gen, Instance)
loadListener p kvars gen x =
    do
     t <- loadTerm kvars x
     return $ mkListener p gen t

loadRest :: Monad m => Pos -> [Term] -> Prot -> Gen -> [Goal] ->
            [Instance] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr ()] -> m Preskel
loadRest pos vars p gen gs insts orderings nr ar ur fs pl comment =
    do
      case null insts of
        True -> fail (shows pos "No strands")
        False -> return ()
      let heights = map height insts
      o <- loadOrderings heights orderings
      nr <- loadBaseTerms vars nr
      ar <- loadBaseTerms vars ar
      ur <- loadBaseTerms vars ur
      fs <- mapM (loadFact heights vars) fs
      let (nr', ar', ur') = foldl addInstOrigs (nr, ar, ur) insts
      prios <- mapM (loadPriorities heights) pl
      let k = mkPreskel gen p gs insts o nr' ar' ur' fs prios comment
      case termsWellFormed $ nr' ++ ar' ++ ur' ++ kterms k of
        False -> fail (shows pos "Terms in skeleton not well formed")
        True -> return ()
      case verbosePreskelWellFormed k of
        Return () -> return k
        Fail msg -> fail $ shows pos
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
      case fst n0 == fst n1 of  -- Same strand
        True -> fail (shows pos "Malformed pair -- nodes in same strand")
        False -> return (n0, n1)
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

loadFact :: Monad m => [Int] -> [Term] -> SExpr Pos -> m Fact
loadFact heights vars (L _ (S _ name : fs)) =
  do
    fs <- mapM (loadFterm heights vars) fs
    return $ Fact name fs
loadFact _ _ x =
  fail (shows (annotation x) "Malformed fact")

loadFterm :: Monad m => [Int] -> [Term] -> SExpr Pos -> m FTerm
loadFterm heights _ (N pos s)
  | 0 <= s && s < length heights = return $ FSid s
  | otherwise = fail (shows pos ("Bad strand in fact: " ++ show s))
loadFterm heights _ x@(L _ [N _ _, N _ _]) =
  do
    n <- loadNode heights x
    return $ FNode n
loadFterm _ vars x =
  do
    t <- loadTerm vars x
    return $ FTerm t

loadPriorities :: Monad m => [Int] -> SExpr Pos -> m (Node, Int)
loadPriorities heights (L _ [x, N _ p]) =
    do
      n <- loadNode heights x
      return (n, p)
loadPriorities _ x =
    fail (shows (annotation x) "Malformed priority")

addInstOrigs :: ([Term], [Term], [Term]) -> Instance ->
                ([Term], [Term], [Term])
addInstOrigs (nr, ar, ur) i =
    (foldl (flip adjoin) nr $ inheritRnon i,
     foldl (flip adjoin) ar $ inheritRpnon i,
     foldl (flip adjoin) ur $ inheritRunique i)

-- Security goals

-- Load a defgoal form
findGoal :: Monad m => Pos -> [Prot] -> [SExpr Pos] -> m Preskel
findGoal pos ps (S _ name : x : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p ->
        do
          (g, goal, antec) <- loadSentence RoleSpec pos p (pgen p) x
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

loadGoals :: Monad m => Pos -> Prot -> Gen -> [SExpr Pos] -> m (Gen, [Goal])
loadGoals _ _ g [] = return (g, [])
loadGoals pos prot g (x : xs) =
  do
    (g, goal, _) <- loadSentence RoleSpec pos prot g x
    (g, goals) <- loadGoals pos prot g xs
    return (g, goal : goals)

data Mode
  = RoleSpec
  | UnusedVars

-- Load a single security goal, a universally quantified formula
-- Returns the goal and the antecedent with position information.

loadSentence :: Monad m => Mode -> Pos -> Prot -> Gen ->
                SExpr Pos -> m (Gen, Goal, Conj)
loadSentence md _ prot g (L pos [S _ "forall", L _ vs, x]) =
  do
    (g, vars) <- loadVars g vs
    loadImplication md pos prot g (L.nub $ reverse vars) x
loadSentence _ pos _ _ _ = fail (shows pos "Bad goal sentence")

-- Load the top-level implication of a security goal

loadImplication :: Monad m => Mode -> Pos -> Prot -> Gen -> [Term] ->
                   SExpr Pos -> m (Gen, Goal, Conj)
loadImplication md _ prot g vars (L pos [S _ "implies", a, c]) =
  do
    antec <- loadRoleSpecific md pos prot vars vars a
    (g, concl) <- loadConclusion md pos prot g vars c
    let goal =
          Goal { uvars = vars,
                 antec = map snd antec,
                 concl = map (map snd) concl }
    return (g, goal, antec)
loadImplication _ pos _ _ _ _ = fail (shows pos "Bad goal implication")

-- The conclusion must be a disjunction.  Each disjunct may introduce
-- existentially quantified variables.

loadConclusion :: Monad m => Mode -> Pos -> Prot -> Gen -> [Term] ->
                  SExpr Pos -> m (Gen, [Conj])
loadConclusion _ _ _ g _ (L _ [S _ "false"]) = return (g, [])
loadConclusion md _ prot g vars (L pos (S _ "or" : xs)) =
  loadDisjuncts md pos prot g vars xs []
loadConclusion md pos prot g vars x =
  do
    (g, a) <- loadExistential md pos prot g vars x
    return (g, [a])

loadDisjuncts :: Monad m => Mode -> Pos -> Prot -> Gen -> [Term] ->
                 [SExpr Pos] -> [Conj] -> m (Gen, [Conj])
loadDisjuncts _ _ _ g _ [] rest = return (g, reverse rest)
loadDisjuncts md pos prot g vars (x : xs) rest =
  do
    (g, a) <- loadExistential md pos prot g vars x
    loadDisjuncts md pos prot g vars xs (a : rest)

loadExistential :: Monad m => Mode -> Pos -> Prot -> Gen -> [Term] ->
                   SExpr Pos -> m (Gen, Conj)
loadExistential md _ prot g vars (L pos [S _ "exists", L _ vs, x]) =
  do
    (g, evars) <- loadVars g vs
    as <- loadRoleSpecific md pos prot (reverse evars ++ vars) evars x
    return (g, as)
loadExistential md pos prot g vars x =
  do
    as <- loadRoleSpecific md pos prot vars [] x
    return (g, as)

--- Load a conjunction of atomic formulas and ensure the formula is
--- role specific or that all declared variables are used.

loadRoleSpecific :: Monad m => Mode -> Pos -> Prot -> [Term] ->
                    [Term] -> SExpr Pos -> m Conj
loadRoleSpecific RoleSpec pos prot vars unbound x =
  do
    as <- loadConjunction pos prot vars x
    let as' = L.sortBy (\(_, x) (_, y) -> aFormOrder x y) as
    unbound <- foldM roleSpecific unbound as'
    case unbound of
      [] -> return as'
      (v : _) -> fail (shows (annotation x) (showst v " not used"))
loadRoleSpecific UnusedVars pos prot vars _ x =
  do
    as <- loadConjunction pos prot vars x
    -- Compute the free variables in the conjunction
    let f vars (_, form) = aFreeVars vars form
    case vars L.\\ foldl f [] as of
      [] -> return as
      (v : _) -> fail (shows (annotation x) (showst v " not used"))

-- Load a conjunction of atomic formulas

loadConjunction :: Monad m => Pos -> Prot -> [Term] ->
                   SExpr Pos -> m Conj
loadConjunction _ p kvars (L pos (S _ "and" : xs)) =
  loadConjuncts pos p kvars xs []
loadConjunction top p kvars x =
  do
    (pos, a) <- loadPrimary top p kvars x
    return [(pos, a)]

loadConjuncts :: Monad m => Pos -> Prot -> [Term] ->
                 [SExpr Pos] -> Conj -> m Conj
loadConjuncts _ _ _ [] rest = return (reverse rest)
loadConjuncts top p kvars (x : xs) rest =
  do
    (pos, a) <- loadPrimary top p kvars x
    loadConjuncts top p kvars xs ((pos, a) : rest)

-- Load the atomic formulas

loadPrimary :: Monad m => Pos -> Prot -> [Term] ->
               SExpr Pos -> m (Pos, AForm)
loadPrimary _ _ kvars (L pos [S _ "=", x, y]) =
  do
    t <- loadTerm kvars x
    t' <- loadTerm kvars y
    return (pos, Equals t t')
loadPrimary _ _ kvars (L pos [S _ "non", x]) =
  do
    t <- loadAlgTerm kvars x
    return (pos, Non t)
loadPrimary _ _ kvars (L pos [S _ "pnon", x]) =
  do
    t <- loadAlgTerm kvars x
    return (pos, Pnon t)
loadPrimary _ _ kvars (L pos [S _ "uniq", x]) =
  do
    t <- loadAlgTerm kvars x
    return (pos, Uniq t)
loadPrimary _ _ kvars (L pos [S _ "uniq-at", x, y, z]) =
  do
    t <- loadAlgTerm kvars x
    t' <- loadNodeTerm kvars y z
    return (pos, UniqAt t t')
loadPrimary _ _ kvars (L pos (S _ "fact" : S _ name : fs)) =
  do
    fs <- mapM (loadFactTerm kvars) fs
    return (pos, AFact name fs)
loadPrimary _ _ kvars (L pos [S _ "prec", w, x, y, z]) =
  do
    t <- loadNodeTerm kvars w x
    t' <- loadNodeTerm kvars y z
    case fst t == fst t' of
      True -> fail (shows pos "Malformed pair -- nodes in same strand")
      False -> return (pos, Prec t t')
loadPrimary _ p kvars (L pos [S _ "p", Q _ name, x, N _ h]) =
  do
    r <- lookupRole pos p name
    t <- loadStrdTerm kvars x
    case h <= 0 || h > length (rtrace r) of
      True -> fail (shows pos "Bad length")
      False -> return (pos, Length r t h)
loadPrimary _ p kvars (L pos [S _ "p", Q _ name, Q var x, y, z]) =
  do
    r <- lookupRole pos p name
    v <- loadAlgTerm (rvars r) (S var x)
    s <- loadStrdTerm kvars y
    t <- loadAlgTerm kvars z
    case isVar v of
      False -> fail (shows pos "Bad parameter -- not a variable")
      True ->
        case firstOccurs v r of
          Just i -> return (pos, Param r v (i + 1) s t)
          Nothing ->
            fail (shows pos ("parameter " ++ x ++ " not in role " ++ name))
loadPrimary _ _ _ (L pos (S _ "p" : Q _ name : _)) =
  fail (shows pos ("Bad role specific formula for role " ++ name))
loadPrimary _ _ _ (L pos (S _ pred : _)) =
  fail (shows pos ("Bad formula for predicate " ++ pred))
loadPrimary pos _ _ _ = fail (shows pos "Bad formula")

-- Load a term and make sure it does not have sort strd

loadAlgTerm :: Monad m => [Term] -> SExpr Pos -> m Term
loadAlgTerm ts x =
  do
    t <- loadTerm ts x
    case isStrdVar t of
      True -> fail (shows (annotation x) "Expecting an algebra term")
      False -> return t

-- Load a term and make sure it has sort strd

loadStrdTerm :: Monad m => [Term] -> SExpr Pos -> m Term
loadStrdTerm ts x =
  do
    t <- loadTerm ts x
    case isStrdVar t of
      True -> return t
      False -> fail (shows (annotation x) "Expecting a strand variable")

-- Load a term and make sure it describes a node

loadNodeTerm :: Monad m => [Term] -> SExpr Pos -> SExpr Pos -> m NodeTerm
loadNodeTerm ts x (N _ i) | i >= 0 =
  do
    t <- loadStrdTerm ts x
    return (t, i)
loadNodeTerm _ _ y =
  fail (shows (annotation y) "Expecting an integer")

-- Load a formula term (FTerm)

loadFactTerm :: Monad m => [Term] -> SExpr Pos -> m FactTerm
loadFactTerm ts (L _ [s, i@(N _ _)]) =
  do
    n <- loadNodeTerm ts s i
    return $ FactNode n
loadFactTerm ts x =
  do
    t <- loadTerm ts x
    return $ FactTerm t

-- Role specific check

termVars :: Term -> [Term]
termVars t = addVars [] t

allBound :: [Term] -> Term -> Bool
allBound unbound t =
  L.all (flip L.notElem unbound) (termVars t)

allFBound :: [Term] -> FactTerm -> Bool
allFBound unbound (FactNode (z, _)) = L.notElem z unbound
allFBound unbound (FactTerm t) = allBound unbound t

-- Returns variables in unbound that are not role specific

roleSpecific :: Monad m => [Term] -> (Pos, AForm) -> m [Term]
roleSpecific unbound (_, Length _ z _) =
  return $ L.delete z unbound
roleSpecific unbound (pos, Param _ _ _ z t)
  | L.notElem z unbound = return $ unbound L.\\ termVars t
  | otherwise = fail (shows pos "Unbound variable in parameter predicate")
roleSpecific unbound (pos, Prec (z, _) (z', _))
  | L.notElem z unbound && L.notElem z' unbound = return unbound
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
roleSpecific unbound (pos, UniqAt t (z, _))
  | allBound unbound t && L.notElem z unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in uniq-at")
roleSpecific unbound (pos, AFact _ fs)
  | all (allFBound unbound) fs = return unbound
  | otherwise = fail (shows pos "Unbound variable in fact")
roleSpecific unbound (pos, Equals t t')
  | isStrdVar t && isStrdVar t' =
    case L.notElem t unbound && L.notElem t' unbound of
      True -> return unbound
      False -> fail (shows pos "Unbound variable in equals")
  | isStrdVar t = fail (shows pos "Type mismatch in equals")
  | isStrdVar t' = fail (shows pos "Type mismatch in equals")
  | allBound unbound t && allBound unbound t' = return unbound
  | otherwise = fail (shows pos "Unbound variable in equals")
