-- Loads formulas from S-expressions as part of the CPSA loader process.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.LoadFormulas
    (loadSentence,
     sortedVarsOfStrings,
     sortedVarsOfNames,
     varsInTerm,
     loadTerms,
     loadFactList, loadDisjuncts, loadConclusions, loadConclusion,
     VarListSpec, Mode(..),
     lookupRole) where

import Control.Monad

import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Signature
import CPSA.Algebra
import CPSA.Protocol
-- import CPSA.Characteristic

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

-- Moved this to Algebra.hs:
-- type VarListSpec = [(String,[String])]

showst :: Term -> ShowS
showst t =
    shows $ displayTerm (addToContext emptyContext [t]) t

sortedVarsOfNames :: Sig -> Gen -> String -> [String] -> (Gen, [Term])
sortedVarsOfNames sig g sortName =
    L.foldr
    (\name (g,vs) ->
         let (g', v) = newVar sig g name sortName in
         (g', (v : vs)))
    (g, [])

sortedVarsOfStrings :: Sig -> Gen -> VarListSpec -> (Gen,[Term])
sortedVarsOfStrings sig g =
    foldr (\(s,varnames) (g,soFar) ->
               let (g', vars) = sortedVarsOfNames sig g s varnames in
               (g', vars ++ soFar))
              (g,[])

varsInTerm :: Term -> [Term]
varsInTerm t =
    foldVars (\vars v -> v : vars) [] t

{--

-- These two next procedures were unused.

varOfName :: MonadFail m => [AForm] -> String -> m Term
varOfName aforms s =
    case (foldr (\aform vars -> filter (((==) s) . varName)
                                $ aFreeVars vars aform)
          []                          -- no vars to begin with
          aforms) of
      [v] -> return v
      [] -> fail ("varOfName:  Variable of name "
                  ++ s ++ "not found in formulas "
                         ++ (show aforms))
      _ -> fail ("varOfName:  Multiple variables of name "
                 ++ s ++ "found in formulas "
                        ++ (show aforms))

-- Given a conjunction (list of AForms) and a variable specification,
-- we would like to retrieve, for each of the variable names in the
-- variable specification, a unique variable occurring in the
-- conjunction with that name.  We return them in the same order as in
-- the variable specification.

-- This procedure fails if there is no variable of a given name, or if
-- there are more than one.

varsOfVarSpecList :: MonadFail m => [AForm] -> VarListSpec -> m [Term]
varsOfVarSpecList aforms [] = return []
varsOfVarSpecList aforms ((_, names) : rest) =
    do
      varsRest <- varsOfVarSpecList aforms rest
      newVars <- (mapM (varOfName aforms) names)
      return (newVars ++ varsRest)

--}

loadTerms :: MonadFail m => Sig -> [Term] -> [SExpr Pos] -> m [Term]
loadTerms sig vars =
    mapM (loadTerm sig vars False)

loadFactList :: MonadFail m => Sig -> [Term] ->
                [SExpr Pos] -> m [(String, [Term])]
loadFactList sig vars =
    mapM (loadAFact sig vars)

loadAFact :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m (String, [Term])
loadAFact sig vars (L _ (S _ name : fs)) =
    do
      fs <- mapM (loadTerm sig vars False) fs
      return $ (name, fs)
loadAFact _ _ x = fail (shows (annotation x) "Malformed fact")

lookupRole :: MonadFail m => Pos -> Prot -> String -> m Role
lookupRole _ p role  | role == "" =
    return $ listenerRole p
lookupRole pos p role =
    case L.find (\r -> role == rname r) (roles p) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname p)
      Just r -> return r

data Mode
  = RoleSpec
  | UnusedVars
  | Liberal

-- Load a single security goal, a universally quantified formula
-- Returns the goal and the antecedent with position information.

loadSentence :: MonadFail m => Sig -> Mode -> Pos -> Prot -> Gen ->
                SExpr Pos -> m (Gen, Goal, Conj)
loadSentence sig md _ prot g (L pos [S _ "forall", L _ vs, x]) =
  do
    (g, vars) <- loadVars sig g vs
    loadImplication sig md pos prot g vars x
loadSentence _ _ pos _ _ _ = fail (shows pos "Bad goal sentence:  No forall")

-- Load the top-level implication of a security goal

loadImplication :: MonadFail m => Sig -> Mode -> Pos -> Prot -> Gen ->
                   [Term] -> SExpr Pos -> m (Gen, Goal, Conj)
loadImplication sig md _ prot g vars (L pos [S _ "implies", a, c]) =
  do
    antec <- loadCheckedConj sig md pos prot vars vars a
    (g, vc) <- loadConclusion sig pos prot g vars c
    let f (evars, form) = (evars, map snd form)
    let consq = map f vc        -- Expunge position info
    let goal =
          Goal { uvars = vars,
                 antec = map snd antec,
                 consq = consq,
                 concl = map snd consq }
    return (g, goal, antec)
loadImplication _ _ pos _ _ _ _ = fail (shows pos "Bad goal implication")

-- To load a number of conclusions from an SExpr

loadConclusions :: MonadFail m => Sig -> Prot -> Gen -> [Term] ->
                  [SExpr Pos] -> m (Gen, [[([Term], Conj)]])
loadConclusions _ _ g _ [] = return (g,[])
loadConclusions sig prot g vars (x : rest) =
    do
      (g,newConcl) <- loadConclusion sig (annotation x) prot g vars x
      (g',concls) <- loadConclusions sig prot g vars rest
      return (g', newConcl : concls)

-- The conclusion must be a disjunction.  Each disjunct may introduce
-- existentially quantified variables.

loadConclusion :: MonadFail m => Sig -> Pos -> Prot -> Gen -> [Term] ->
                  SExpr Pos -> m (Gen, [([Term], Conj)])
loadConclusion _ _ _ g _ (L _ [S _ "false"]) = return (g, [])
loadConclusion sig _ prot g vars (L pos (S _ "or" : xs)) =
  loadDisjuncts sig pos prot g vars xs []
loadConclusion sig pos prot g vars x =
  do
    (g, a) <- loadExistential sig pos prot g vars x
    return (g, [a])

loadDisjuncts :: MonadFail m => Sig -> Pos -> Prot -> Gen -> [Term] ->
                 [SExpr Pos] -> [([Term], Conj)] -> m (Gen, [([Term], Conj)])
loadDisjuncts _ _ _ g _ [] rest = return (g, reverse rest)
loadDisjuncts sig pos prot g vars (x : xs) rest =
  do
    (g, a) <- loadExistential sig pos prot g vars x
    loadDisjuncts sig pos prot g vars xs (a : rest)

loadExistential :: MonadFail m => Sig -> Pos -> Prot -> Gen -> [Term] ->
                   SExpr Pos -> m (Gen, ([Term], Conj))
loadExistential sig _ prot g vars (L pos [S _ "exists", L _ vs, x]) =
  do
    (g, evars) <- loadVars sig g vs
    as <- loadCheckedConj sig -- RoleSpec
          --UnusedVars
          Liberal pos prot (evars ++ vars) evars x
    return (g, (evars, as))
loadExistential sig pos prot g vars x =
  do
    as <- loadCheckedConj sig RoleSpec pos prot vars [] x
    return (g, ([], as))

-- Load a conjunction and check the result as determined by the mode
-- md.

loadCheckedConj :: MonadFail m => Sig -> Mode -> Pos -> Prot -> [Term] ->
                   [Term] -> SExpr Pos -> m Conj
loadCheckedConj sig RoleSpec pos prot vars unbound x =
  loadRoleSpecific sig pos prot vars unbound x
loadCheckedConj sig UnusedVars pos prot vars unbound x =
  loadUsedVars sig pos prot vars unbound x
loadCheckedConj sig Liberal pos prot vars unbound x =
  loadLiberalVars sig pos prot vars unbound x

--- Load a conjunction of atomic formulas and ensure the formula is
--- role specific.

loadRoleSpecific :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                    [Term] -> SExpr Pos -> m Conj
loadRoleSpecific sig pos prot vars unbound x =
  do
    as <- loadConjunction sig pos prot vars x
    let as' = L.sortBy (\(_, x) (_, y) -> aFormOrder x y) as
    -- Remove vars that are in facts
    let unbound' = foldl factSpecific unbound as'
    unbound <- foldM roleSpecific unbound' as'
    case unbound of
      [] -> return as'
      (v : _) -> fail (shows (annotation x) (showst v " not used"))

-- Load a conjunction of atomic formulas and ensure that all declared
-- variables are used.

loadUsedVars :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                [Term] -> SExpr Pos -> m Conj
loadUsedVars sig pos prot vars unbound x =
  do
    as <- loadConjunction sig pos prot vars x
    -- Compute the free variables in the conjunction
    let f vars (_, form) = aFreeVars vars form
    case unbound L.\\ foldl f [] as of
      [] -> return as
      (v : _) -> fail (shows (annotation x) (showst v " not used"))

-- Load a conjunction of atomic formulas, but don't ensure that all
-- declared variables are used.

loadLiberalVars :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                [Term] -> SExpr Pos -> m Conj
loadLiberalVars sig pos prot vars _ x =
  do
    as <- loadConjunction sig pos prot vars x
    return as

-- Load a conjunction of atomic formulas
loadConjunction :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                   SExpr Pos -> m Conj
loadConjunction sig _ p kvars (L pos (S _ "and" : xs)) =
  loadConjuncts sig pos p kvars xs []
loadConjunction sig top p kvars x =
  do
    posa <- loadConjuncts sig top p kvars [x] []
    return posa

loadConjuncts :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                 [SExpr Pos] -> Conj -> m Conj
loadConjuncts _ _ _ _ [] rest = return (reverse rest)
-- If the head is a strand formula treat it specially
loadConjuncts sig _ p kvars ((L pos (S _ "strand" : ss)) : xs) rest =
  do
    posas <- loadStrand sig pos p kvars ss
    loadConjuncts sig pos p kvars xs (posas ++ rest)
-- If the head is a listener formula treat it specially
loadConjuncts sig _ p kvars ((L pos (S _ "listener" : ss)) : xs) rest =
  do
    posas <- loadListener sig pos p kvars ss
    loadConjuncts sig pos p kvars xs (posas ++ rest)
loadConjuncts sig top p kvars (x : xs) rest =
  do
    (pos, a) <- loadPrimary sig top p kvars x
    loadConjuncts sig top p kvars xs ((pos, a) : rest)

-- Load a strand formula
loadStrand :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> [SExpr Pos] -> m Conj
loadStrand sig _ p kvars (S pos name : x : N _ h : vmaps) =
  do
    r <- lookupRole pos p name
    s <- loadStrdTerm sig kvars x
    case h <= 0 || h > length (rtrace r) of
      True -> fail (shows pos "Bad length")
      False ->
        do
          params <- loadVMaps sig pos p kvars r s h vmaps
          return ((pos, Length r s (indxOfInt h)) : params)
loadStrand _ pos _ _ _ = fail (shows pos "Bad strand formula")

-- Load a listener formula
loadListener :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> [SExpr Pos] -> m Conj
loadListener sig pos p kvars [S pos1 x, S pos2 y] =
  do
    let r = listenerRole p
    v <- loadAlgChanTerm sig (rvars r) (S pos "x")
    s <- loadStrdTerm sig kvars (S pos1 x)
    t <- loadAlgChanTerm sig kvars (S pos2 y)
    return [(pos1, Length r s (indxOfInt 2)), (pos2, Param r v 2 s t)]
loadListener _ pos _ _ _ = fail (shows pos "Bad listener formula")

loadVMaps :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
             Role -> Term -> Int -> [SExpr Pos] -> m Conj
loadVMaps _ _ _ _ _ _ _ [] = return []
loadVMaps sig _ p kvars r s h ((L pos [S var rv, sv]) : vmaps) =
  do
    v <- loadAlgChanTerm sig (rvars r) (S var rv)
    t <- loadAlgChanTerm sig kvars sv
    case isVar v of
      False -> fail (shows pos ("Bad parameter -- not a variable " ++ (show v)))
      True ->
        case firstOccurs v r of
          Just i ->
            do
              rest <- loadVMaps sig pos p kvars r s h vmaps
              return ((pos, Param r v (i + 1) s t) : rest)
          Nothing ->
            fail (shows pos ("parameter " ++ rv ++ " not in role " ++ rname r))
loadVMaps _ pos _ _ _ _ _ _ = fail (shows pos "Bad variable map")

-- Load the atomic formulas

loadPrimary :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
               SExpr Pos -> m (Pos, AForm)
loadPrimary sig _ _ kvars (L pos [S _ "=", x, y]) =
  do
    t <- loadTerm sig kvars False x
    t' <- loadTerm sig kvars False y
    case isStrdVar t == isStrdVar t' of
      True -> return (pos, Equals t t')
      False -> fail (shows pos "Sort mismatch in equality")
loadPrimary sig _ _ kvars (L pos [S _ "component", x, y]) =
  do
    t <- loadTerm sig kvars False x
    t' <- loadTerm sig kvars False y
    case isStrdVar t || isStrdVar t' of
      True -> fail (shows pos "Strand variable in component formula")
      False -> return (pos, Component t t')
loadPrimary sig _ _ kvars (L pos [S _ "non", x]) =
  do
    t <- loadAlgTerm sig kvars x
    return (pos, Non t)
loadPrimary sig _ _ kvars (L pos [S _ "pnon", x]) =
  do
    t <- loadAlgTerm sig kvars x
    return (pos, Pnon t)
loadPrimary sig _ _ kvars (L pos [S _ "uniq", x]) =
  do
    t <- loadAlgTerm sig kvars x
    return (pos, Uniq t)
loadPrimary sig _ _ kvars (L pos [S _ "uniq-at", x, y, z]) =
  do
    t <- loadAlgTerm sig kvars x
    t' <- loadNodeTerm sig kvars y z
    return (pos, UniqAt t t')
loadPrimary sig _ _ kvars (L pos [S _ "ugen", x]) =
  do
    t <- loadAlgTerm sig kvars x
    return (pos, Ugen t)
loadPrimary sig _ _ kvars (L pos [S _ "ugen-at", x, y, z]) =
  do
    t <- loadAlgTerm sig kvars x
    t' <- loadNodeTerm sig kvars y z
    return (pos, UgenAt t t')
loadPrimary sig _ _ kvars (L pos [S _ "gen-st", x]) =
  do
    t <- loadAlgTerm sig kvars x
    return (pos, GenStV t)
loadPrimary sig _ _ kvars (L pos [S _ "conf", x]) =
  do
    t <- loadChanTerm sig kvars x
    return (pos, Conf t)
loadPrimary sig _ _ kvars (L pos [S _ "auth", x]) =
  do
    t <- loadChanTerm sig kvars x
    return (pos, Auth t)
loadPrimary sig _ _ kvars (L pos (S _ "fact" : S _ name : fs)) =
  do
    fs <- loadTerms sig kvars fs
    return (pos, AFact name fs)
loadPrimary sig _ _ kvars (L pos [S _ "comm-pr", w, x, y, z]) =
  do
    t <- loadNodeTerm sig kvars w x
    t' <- loadNodeTerm sig kvars y z
    return (pos, Commpair t t')
loadPrimary sig _ _ kvars (L pos [S _ "same-locn", w, x, y, z]) =
  do
    t <- loadNodeTerm sig kvars w x
    t' <- loadNodeTerm sig kvars y z
    return (pos, SameLocn t t')
loadPrimary sig _ _ kvars (L pos [S _ "state-node", w, x]) =
  do
    t <- loadNodeTerm sig kvars w x
    return (pos, StateNode t)
loadPrimary sig _ _ kvars (L pos [S _ "trans", w, x]) =
  do
    t <- loadNodeTerm sig kvars w x
    return (pos, Trans t)
loadPrimary sig _ _ kvars (L pos [S _ "leads-to", w, x, y, z]) =
  do
    t <- loadNodeTerm sig kvars w x
    t' <- loadNodeTerm sig kvars y z
    return (pos, LeadsTo t t')

loadPrimary sig _ _ kvars (L pos [S _ "prec", w, x, y, z]) =
  do
    t <- loadNodeTerm sig kvars w x
    t' <- loadNodeTerm sig kvars y z
    case fst t == fst t' of
      True -> fail (shows pos "Malformed pair -- nodes in same strand")
      False -> return (pos, Prec t t')
loadPrimary sig _ p kvars (L pos [S _ "p", Q _ name, x, N _ h]) =
  do
    r <- lookupRole pos p name
    t <- loadStrdTerm sig kvars x
    case h <= 0 || h > length (rtrace r) of
      True -> fail (shows pos "Bad length")
      False -> return (pos, Length r t (indxOfInt h))
loadPrimary sig _ p kvars (L pos [S _ "p", Q _ name, x, ht]) =
  do
    r <- lookupRole pos p name
    t <- loadStrdTerm sig kvars x
    h <- loadTerm sig kvars False ht
    return (pos, Length r t h)
loadPrimary sig _ p kvars (L pos [S _ "p", Q _ name, Q var x, y, z]) =
  do
    r <- lookupRole pos p name
    v <- loadAlgChanTerm sig (rvars r) (S var x)
    s <- loadStrdTerm sig kvars y
    t <- loadAlgChanTerm sig kvars z
    case isVar v of
      False -> fail (shows pos ("Bad parameter -- not a variable" ++ (show v)))
      True ->
        case firstOccurs v r of
          Just i -> return (pos, Param r v (i + 1) s t)
          Nothing ->
            fail (shows pos ("parameter " ++ x ++ " not in role " ++ name))
loadPrimary _ _ _ _ (L pos (S _ "p" : Q _ name : _)) =
  fail (shows pos ("Bad protocol specific formula for role " ++ name))
loadPrimary _ _ _ _ (L pos (S _ pred : _)) =
  fail (shows pos ("Bad formula for predicate " ++ pred))
loadPrimary _ pos _ _ _ = fail (shows pos "Bad formula")

-- Load a term and make sure it does not have sort strd, indx, locn, or chan

loadAlgTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadAlgTerm sig ts x =
  do
    t <- loadTerm sig ts False x
    case isStrdVar t || isIndxVar t || isIndxConst t || isChan t || isLocn t of
      True -> fail (shows (annotation x) "Expecting an algebra term")
      False -> return t
-- Load a term and make sure it does not have sort strd, or indx

loadAlgChanTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadAlgChanTerm sig ts x =
  do
    t <- loadTerm sig ts False x
    case isStrdVar t || isIndxVar t || isIndxConst t of
      True -> fail (shows (annotation x)
                    "Expecting an algebra term or a channel")
      False -> return t

-- Load a term and make sure it has sort chan

loadChanTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadChanTerm sig ts x =
  do
    t <- loadTerm sig ts False x
    case isChan t of
      True -> return t
      False -> fail (shows (annotation x) "Expecting a channel variable")

-- Load a term and make sure it has sort strd

loadStrdTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadStrdTerm sig ts x =
  do
    t <- loadTerm sig ts False x
    case isStrdVar t of
      True -> return t
      False -> fail (shows (annotation x) "Expecting a strand variable")

-- Load a term and make sure it has sort indx

loadIndxTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadIndxTerm sig ts x =
  do
    t <- loadTerm sig ts False x
    case isIndxVar t of
      True -> return t
      False ->
        case isIndxConst t of
          True -> return t
          False -> fail (shows (annotation x) "Expecting an indx variable")

-- Load a term and make sure it describes a node

loadNodeTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos ->
                SExpr Pos -> m NodeTerm
loadNodeTerm sig ts x (N _ i) | i >= 0 =
  do
    t <- loadStrdTerm sig ts x
    return (t, indxOfInt i)
loadNodeTerm sig ts x v =
  do
    t <- loadStrdTerm sig ts x
    t' <- loadIndxTerm sig ts v
    return (t, t')

-- Role specific check

termVars :: Term -> [Term]
termVars t = addVars [] t

allBound :: [Term] -> Term -> Bool
allBound unbound t =
  L.all (flip L.notElem unbound) (termVars t)

-- Returns variables in unbound that are not role specific

roleSpecific :: MonadFail m => [Term] -> (Pos, AForm) -> m [Term]
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
roleSpecific unbound (pos, Ugen t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in ugen")
roleSpecific unbound (pos, UgenAt t (z, _))
  | allBound unbound t && L.notElem z unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in ugen-at")
roleSpecific unbound (pos, GenStV t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in gen-st")
roleSpecific unbound (pos, Conf t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in conf")
roleSpecific unbound (pos, Auth t)
  | allBound unbound t = return unbound
  | otherwise = fail (shows pos "Unbound variable in auth")
roleSpecific unbound (pos, AFact _ fs)
  | all (allBound unbound) fs = return unbound
  | otherwise = fail (shows pos "Unbound variable in fact")
roleSpecific unbound (pos, Commpair (z, _) (z', _))
  | L.notElem z unbound && L.notElem z' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in comm-pr")
roleSpecific unbound (pos, LeadsTo (z, _) (z', _))
  | L.notElem z unbound && L.notElem z' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in leads-to")
roleSpecific unbound (pos, StateNode (z, _))
  | L.notElem z unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in state-node")
roleSpecific unbound (pos, Trans (z, _))
  | L.notElem z unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in trans")
roleSpecific unbound (pos, SameLocn (z, i) (z', i'))
  | L.notElem z unbound && L.notElem z' unbound &&
    L.notElem i unbound && L.notElem i' unbound = return unbound
  | otherwise = fail (shows pos "Unbound variable in same-locn")

roleSpecific unbound (pos, Equals t t')
  | isStrdVar t && isStrdVar t' =
    case L.notElem t unbound && L.notElem t' unbound of
      True -> return unbound
      False -> fail (shows pos "Unbound variable in equals")
  | isStrdVar t = fail (shows pos "Type mismatch in equals")
  | isStrdVar t' = fail (shows pos "Type mismatch in equals")
  | allBound unbound t && allBound unbound t' = return unbound
  | otherwise = fail (shows pos "Unbound variable in equals")

roleSpecific unbound (pos, Component t t')
  | isStrdVar t && isStrdVar t' =
    case L.notElem t unbound && L.notElem t' unbound of
      True -> return unbound
      False -> fail (shows pos "Unbound variable in component")
  | isStrdVar t = fail (shows pos "Type mismatch in component")
  | isStrdVar t' = fail (shows pos "Type mismatch in component")
  | allBound unbound t && allBound unbound t' = return unbound
  | otherwise = fail (shows pos "Unbound variable in component")

-- Remove unbound message variables that occur in a fact
factSpecific :: [Term] -> (Pos, AForm) -> [Term]
factSpecific unbound (_, AFact _ fs) =
  unbound L.\\ foldl addVars [] (L.filter (not . isStrdVar) fs)
factSpecific unbound _ = unbound
