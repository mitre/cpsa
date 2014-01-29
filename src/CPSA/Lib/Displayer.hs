-- Displays protocols and preskeletons as S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Displayer (displayProt, displayPreskel, displayNode) where

import qualified Data.List as L
import qualified Data.Set as S
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Strand

-- Display of protocols

displayProt :: Algebra t p g s e c => Prot t g -> SExpr ()
displayProt p =
    L () (S () "defprotocol" : S () (pname p) : S () (alg p) : rs)
    where
      rs = foldl f (pcomment p) (reverse (roles p))
      f rs r = displayRole r : rs

displayRole :: Algebra t p g s e c => Role t -> SExpr ()
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

varsContext :: Algebra t p g s e c => [t] -> c
varsContext vars =
    addToContext emptyContext vars

displayTerms :: Algebra t p g s e c => c -> [t] -> [SExpr ()]
displayTerms ctx ts = map (displayTerm ctx) (L.sort ts)

displayLenTerms :: Algebra t p g s e c => c -> [(Maybe Int, t)] -> [SExpr ()]
displayLenTerms ctx ts = map (displayLenTerm ctx) (L.sort ts)

displayLenTerm :: Algebra t p g s e c => c -> (Maybe Int, t) -> SExpr ()
displayLenTerm ctx (Nothing, t) = displayTerm ctx t
displayLenTerm ctx (Just len, t) = L () [N () len, displayTerm ctx t]

displayOptional :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]
displayOptional _ [] rest = rest
displayOptional key value rest =
    L () (S () key : value) : rest

displayTrace :: Algebra t p g s e c => c ->
                Trace t -> [SExpr ()]
displayTrace ctx trace =
    map displayDt trace
    where
      displayDt (In t) = L () [S () "recv", displayTerm ctx t]
      displayDt (Out t) = L () [S () "send", displayTerm ctx t]

-- Display of preskeletons

displayPreskel :: Algebra t p g s e c => Preskel t g s e ->
                  [SExpr ()] -> SExpr ()
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
displayRest :: Algebra t p g s e c => Preskel t g s e ->
               c -> [SExpr ()] -> [SExpr ()]
displayRest k ctx rest =
    displayOptional "precedes" (displayOrdering (orderings k))
     (displayOptional "non-orig" (displayTerms ctx (knon k))
      (displayOptional "pen-non-orig" (displayTerms ctx (kpnon k))
       (displayOptional "uniq-orig" (displayTerms ctx (kunique k))
        (displayOptional "priority" priorities
         (kcomment k ++
          (displayOperation k ctx
           (displayOptional "traces" traces rest)))))))
    where
      priorities = map displayPriority (kpriority k)
      traces = map (L () . displayTrace ctx . trace) (insts k)

displayPriority :: (Node, Int) -> SExpr ()
displayPriority (n, p) =
    L () [displayNode n, N () p]

displayInst :: Algebra t p g s e c => c ->
               Instance t e -> SExpr ()
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

displayMaplet :: Algebra t p g s e c => c -> c -> (t, t) -> SExpr ()
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
displayOperation :: Algebra t p g s e c => Preskel t g s e ->
                    c -> [SExpr ()] -> [SExpr ()]
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
displayOpTerm :: Algebra t p g s e c => c -> t -> SExpr ()
displayOpTerm ctx t = displayTerm (addToContext ctx [t]) t

displayOpTerms :: Algebra t p g s e c => c -> [t] -> [SExpr ()]
displayOpTerms ctx ts = map (displayTerm (addToContext ctx ts)) (L.sort ts)
