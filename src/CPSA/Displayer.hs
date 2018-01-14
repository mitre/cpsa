-- Displays protocols and preskeletons as S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Displayer (displayProt, displayPreskel, displayNode) where

import qualified Data.List as L
import qualified Data.Set as S
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Protocol
import CPSA.Strand

-- Display of protocols

displayProt :: Prot -> SExpr ()
displayProt p =
    L () (S () "defprotocol" : S () (pname p) : S () (alg p) : rs)
    where
      rs = foldl f (map displayRule (rules p) ++ pcomment p)
                   (reverse (roles p))
      f rs r = displayRole r : rs

displayRule :: Rule -> SExpr ()
displayRule r =
  L () (S () "defrule" :
        S () (uname r) :
        L () [S () "implies",
              displayConj (uantec r),
              displayDisj (uconcl r)] :
        ucomment r)

displayDisj :: [[UForm]] -> SExpr ()
displayDisj [] = error "DisplayDisj: no conclusion"
displayDisj [conj] = displayConj conj
displayDisj disj =
  L () (S () "or" : map displayConj disj)

displayConj :: [UForm] -> SExpr ()
displayConj [] = L () [S () "false"]
displayConj [form] = displayForm form
displayConj forms = L () (S () "and" : map displayForm forms)

displayForm :: UForm -> SExpr ()
displayForm (ULen r s l) =
  L () [S () "p", Q () (rname r), S () s, N () l]
displayForm (UParam r p _ s t) =
  L () [S () "p", Q () (rname r), displayParam r p,
        S () s, displayUTerm t]
displayForm (UPrec n1 n2) =
  L () [S () "prec", displayUTerm (UNode n1), displayUTerm (UNode n2)]
displayForm (UNon t) =
  L () [S () "non", displayUTerm t]
displayForm (UPnon t) =
  L () [S () "pnon", displayUTerm t]
displayForm (UUniq t) =
  L () [S () "uniq", displayUTerm t]
displayForm (UFact name fs) =
  L () (S () "fact" : S () name : map displayUTerm fs)
displayForm (UEquals t1 t2) =
  L () [S () "=", displayUTerm t1, displayUTerm t2]

displayParam :: Role -> Term -> SExpr ()
displayParam r t =
  case displayTerm (varsContext (rvars r)) t of
    S () var -> Q () var
    _ -> error "displayParam: bad parameter"

displayUTerm :: UTerm -> SExpr ()
displayUTerm (UVar v) = S () v
displayUTerm (UInv v) = L () [S () "invk", S () v]
displayUTerm (UNode (v, i)) = L () [S () v, N () i]

-- Display of roles

displayRole :: Role -> SExpr ()
displayRole r =
    L () (S () "defrole" :
          S () (rname r) :
          L () (S () "vars" : displayVars ctx vars) :
          L () (S () "trace" : displayTrace ctx (rtrace r)) :
          displayOptional "non-orig" (displayLenTerms ctx (rnon r))
          (displayOptional "pen-non-orig" (displayLenTerms ctx (rpnon r))
           (displayOptional "uniq-orig" (displayTerms ctx (runique r))
           (rcomment r))))
    where
      ctx = varsContext vars
      vars = rvars r

varsContext :: [Term] -> Context
varsContext vars =
    addToContext emptyContext vars

displayTerms :: Context -> [Term] -> [SExpr ()]
displayTerms ctx ts = map (displayTerm ctx) (L.sort ts)

displayLenTerms :: Context -> [(Maybe Int, Term)] -> [SExpr ()]
displayLenTerms ctx ts = map (displayLenTerm ctx) (L.sort ts)

displayLenTerm :: Context -> (Maybe Int, Term) -> SExpr ()
displayLenTerm ctx (Nothing, t) = displayTerm ctx t
displayLenTerm ctx (Just len, t) = L () [N () len, displayTerm ctx t]

displayOptional :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]
displayOptional _ [] rest = rest
displayOptional key value rest =
    L () (S () key : value) : rest

displayTrace :: Context -> Trace -> [SExpr ()]
displayTrace ctx trace =
    map displayDt trace
    where
      displayDt (In t) = L () [S () "recv", displayTerm ctx t]
      displayDt (Out t) = L () [S () "send", displayTerm ctx t]

-- Display of preskeletons

displayPreskel :: Preskel -> [SExpr ()] -> SExpr ()
displayPreskel k rest =
    L () (S () "defskeleton" :
          S () (pname (protocol k)) :
          L () (S () "vars" : displayVars ctx vars) :
          foldr f (displayRest k ctx rest) (insts k))
    where
      ctx = varsContext vars
      vars = kvars k
      f i rest = displayInst ctx i : rest

-- Display the remainder of a preskeleton
displayRest :: Preskel -> Context -> [SExpr ()] -> [SExpr ()]
displayRest k ctx rest =
    displayOptional "precedes" (displayOrdering (orderings k))
     (displayOptional "non-orig" (displayTerms ctx (knon k))
      (displayOptional "pen-non-orig" (displayTerms ctx (kpnon k))
       (displayOptional "uniq-orig" (displayTerms ctx (kunique k))
        (displayOptional "facts" (map (displayFact ctx) (kfacts k))
         (displayOptional "priority" priorities
          (kcomment k ++
           (displayOperation k ctx
            (displayOptional "traces" traces rest))))))))
    where
      priorities = map displayPriority (kpriority k)
      traces = map (L () . displayTrace ctx . trace) (insts k)

displayFact :: Context -> Fact -> SExpr ()
displayFact ctx (Fact name fs) =
  L () (S () name : map (displayFterm ctx) fs)

displayFterm :: Context -> FTerm -> SExpr ()
displayFterm _ (FSid s) = N () s
displayFterm _ (FNode n) = displayNode n
displayFterm ctx (FTerm t) = displayTerm ctx t

displayPriority :: (Node, Int) -> SExpr ()
displayPriority (n, p) =
    L () [displayNode n, N () p]

displayInst :: Context -> Instance -> SExpr ()
displayInst ctx s =
    case listenerTerm s of
      Just t -> L () [S () "deflistener", displayTerm ctx t]
      Nothing ->
          L () (S () "defstrand" :
                S () (rname r) :
                N () (height s) :
                map (displayMaplet rctx ctx) maplets)
          where
            r = role s
            domain = rvars r
            maplets = L.sort (reify domain (env s))
            rctx = varsContext domain

displayMaplet :: Context -> Context -> (Term, Term) -> SExpr ()
displayMaplet domain range (x, t)=
    L () [displayTerm domain x, displayTerm range t]

displayOrdering :: [Pair] -> [SExpr ()]
displayOrdering orderings =
    map displayPair (L.sort orderings)

displayPair :: Pair -> SExpr ()
displayPair (n0, n1) =
    L () [displayNode n0, displayNode n1]

displayNode :: Node -> SExpr ()
displayNode (s, p) = L () [N () s, N () p]

-- Display the reason the preskeleton was created
displayOperation :: Preskel -> Context -> [SExpr ()] -> [SExpr ()]
displayOperation k ctx rest =
    case operation k of
      New -> rest
      Contracted subst cause ->
          let substitution = displaySubst ctx subst in
          displayCause (L () (S () "contracted" : substitution)) cause
      Displaced s s' role height cause ->
          displayCause
          (L () [S () "displaced", N () s, N () s', S () role, N () height])
          cause
      AddedStrand role height cause ->
          displayCause
          (L () [S () "added-strand", S () role, N () height]) cause
      AddedListener t cause ->
          displayCause (L () [S () "added-listener", displayOpTerm ctx t]) cause
      Generalized method ->
          let desc = displayMethod ctx method in
          L () (S () "operation" : S () "generalization" : desc) : rest
      Collapsed s s' ->
          let desc = [N () s, N () s'] in
          L () (S () "operation" : S () "collapsed" : desc) : rest
    where
      displayCause op (Cause dir node critical escape) =
          L () (S () "operation" :
                displayDirection dir :
                op :
                displayOpTerm ctx critical :
                displayNode node :
                displayOpTerms ctx (S.toList escape)) : rest
      displayDirection Encryption = S () "encryption-test"
      displayDirection Nonce = S () "nonce-test"
      displayMethod _ (Deleted node) =
          [S () "deleted", displayNode node]
      displayMethod _ (Weakened (n0, n1)) =
          [S () "weakened", L () [displayNode n0, displayNode n1] ]
      displayMethod ctx (Separated t) =
          [S () "separated", displayOpTerm ctx t]
      displayMethod ctx (Forgot t) =
          [S () "forgot", displayOpTerm ctx t]

-- Terms in the operation field may contain variables not in the skeleton
displayOpTerm :: Context -> Term -> SExpr ()
displayOpTerm ctx t = displayTerm (addToContext ctx [t]) t

displayOpTerms :: Context -> [Term] -> [SExpr ()]
displayOpTerms ctx ts = map (displayTerm (addToContext ctx ts)) (L.sort ts)
