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
import CPSA.Channel
import CPSA.Protocol
import CPSA.Strand

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

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
        S () (rlname r) :
        displayGoal (rlgoal r) :
        rlcomment r)

displayGoal :: Goal -> SExpr ()
displayGoal g =
  L () [S () "forall",
        L () (displayVars ctx vars),
        displayImpl ctx g]
  where
    ctx = varsContext vars
    vars = uvars g

displayImpl :: Context -> Goal -> SExpr ()
displayImpl ctx g =
  L () [S () "implies",
        displayConj ctx (antec g),
        displayDisj ctx (consq g) ]

displayDisj :: Context -> [([Term], [AForm])] -> SExpr ()
displayDisj _ [] = L () [S () "false"]
displayDisj ctx [conj] = displayExistential ctx conj
displayDisj ctx disj =
  L () (S () "or" : map (displayExistential ctx) disj)

displayExistential :: Context -> ([Term], [AForm]) -> SExpr ()
displayExistential ctx ([], conj) =
  displayConj ctx conj
displayExistential ctx (evars, conj) =
  L () [S () "exists",
        L () (displayVars ctx' evars),
        displayConj ctx' conj]
  where
    ctx' = addToContext ctx evars

displayConj :: Context -> [AForm] -> SExpr ()
-- displayConj _ [] = error "DisplayConj: empty conjunction"
displayConj ctx [form] = displayForm ctx form
displayConj ctx forms = L () (S () "and" : map (displayForm ctx) forms)

displayForm :: Context -> AForm -> SExpr ()
displayForm ctx (Length r s l) =
  L () [S () "p", Q () (rname r), displayTerm ctx  s, displayTerm ctx l]
displayForm ctx (Param r p _ s t) =
  L () [S () "p", Q () (rname r), displayParam r p,
        displayTerm ctx s, displayTerm ctx t]
displayForm ctx (Prec (x, i) (y, j)) =
  L () [S () "prec", displayTerm ctx x, displayTerm ctx i,
        displayTerm ctx y, displayTerm ctx j]
displayForm ctx (Non t) =
  L () [S () "non", displayTerm ctx t]
displayForm ctx (Pnon t) =
  L () [S () "pnon", displayTerm ctx t]
displayForm ctx (Uniq t) =
  L () [S () "uniq", displayTerm ctx t]
displayForm ctx (UniqAt t (s, i)) =
  L () [S () "uniq-at", displayTerm ctx t,
        displayTerm ctx s, displayTerm ctx i]
displayForm ctx (GenStV t) =
  L () [S () "gen-st", displayTerm ctx t]
displayForm ctx (Conf t) =
  L () [S () "conf", displayTerm ctx t]
displayForm ctx (Auth t) =
  L () [S () "auth", displayTerm ctx t]
displayForm ctx (AFact name fs) =
  L () (S () "fact" : S () name : map (displayTerm ctx) fs)
displayForm ctx (Equals t1 t2) =
  L () [S () "=", displayTerm ctx t1, displayTerm ctx t2]
displayForm ctx (Component t1 t2) =
  L () [S () "component", displayTerm ctx t1, displayTerm ctx t2]
displayForm ctx (Commpair (i,j) (i',j')) =
    L () [S () "comm-pr",
            displayTerm ctx i, displayTerm ctx j,
            displayTerm ctx i', displayTerm ctx j']
displayForm ctx (SameLocn (i,j) (i',j')) =
    L () [S () "same-locn",
            displayTerm ctx i, displayTerm ctx j,
            displayTerm ctx i', displayTerm ctx j']
displayForm ctx (StateNode (i,j)) =
    L () [S () "state-node",
            displayTerm ctx i, displayTerm ctx j]
displayForm ctx (Trans (i,j)) =
    L () [S () "trans",
            displayTerm ctx i, displayTerm ctx j]
displayForm ctx (LeadsTo (i,j) (i',j')) =
    L () [S () "leads-to",
            displayTerm ctx i, displayTerm ctx j,
            displayTerm ctx i', displayTerm ctx j']


    

displayParam :: Role -> Term -> SExpr ()
displayParam r t =
  case displayTerm (varsContext (rvars r)) t of
    S () var -> Q () var
    _ -> error "displayParam: bad parameter"

-- Display of roles

sansPts :: [Term] -> [Term]
sansPts = filter notPt

sansNestedPts :: [(Maybe Int, Term)] -> [(Maybe Int, Term)]
sansNestedPts = filter (\(_,t) -> notPt t)

sansPtMaplets :: [(Term, Term)] -> [(Term, Term)]
sansPtMaplets = filter (\(v,_) -> notPt v)


displayRole :: Role -> SExpr ()
displayRole r =
    L () (S () "defrole" :
          S () (rname r) :
          L () (S () "vars" : displayVars ctx (sansPts vars)) :
          L () (S () "trace" : displayTraceNoPt ctx (rtrace r)) :
          displayOptional "non-orig" (displayLenTerms ctx (sansNestedPts (rnon r)))
          (displayOptional "pen-non-orig" (displayLenTerms ctx (sansNestedPts (rpnon r)))
           (displayOptional "uniq-orig" (displayTerms ctx (sansPts (runique r)))
            (displayOptional "conf" (displayTerms ctx (rconf r))
             (displayOptional "auth" (displayTerms ctx (rauth r))
              (rcomment r))))))
    where
      ctx = varsContext $ rvars r
      vars = sansPts $ rvars r

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
      displayDt (In (Plain t)) =
        L () [S () "recv", displayTerm ctx t]
      displayDt (In (ChMsg ch t)) =
          case isLocn ch of
            True ->  L () [S () "load", displayTerm ctx ch, displayTerm ctx t]
            False -> L () [S () "recv", displayTerm ctx ch, displayTerm ctx t]
      displayDt (Out (Plain t)) =
        L () [S () "send", displayTerm ctx t]
      displayDt (Out (ChMsg ch t)) =
          case isLocn ch of
            True ->  L () [S () "stor", displayTerm ctx ch, displayTerm ctx t]
            False -> L () [S () "send", displayTerm ctx ch, displayTerm ctx t]

displayTraceNoPt :: Context -> Trace -> [SExpr ()]
displayTraceNoPt ctx trace =
    map displayDt trace
    where
      displayDt (In (Plain t)) =
        L () [S () "recv", displayTerm ctx t]
      displayDt (In (ChMsg ch t)) =
          case isLocn ch of
            True ->  L () [S () "load", displayTerm ctx ch, displayTermNoPt ctx t]
            False -> L () [S () "recv", displayTerm ctx ch, displayTerm ctx t]
      displayDt (Out (Plain t)) =
        L () [S () "send", displayTerm ctx t]
      displayDt (Out (ChMsg ch t)) =
          case isLocn ch of
            True ->  L () [S () "stor", displayTerm ctx ch, displayTermNoPt ctx t]
            False -> L () [S () "send", displayTerm ctx ch, displayTerm ctx t]



-- Display of preskeletons

displayPreskel :: Preskel -> [SExpr ()] -> SExpr ()
displayPreskel k rest =
    L () (S () "defskeleton" :
          S () (pname (protocol k)) :
          L () (S () "vars" : displayVars ctx vars ) :
               -- (sansPts vars) lets
               -- try printing points
                foldr f (displayRest k ctx rest) (insts k))
    where
      ctx = varsContext vars 
      vars = kfvars k ++ kvars k
      f i rest = displayInst ctx i : rest

-- Display the remainder of a preskeleton
displayRest :: Preskel -> Context -> [SExpr ()] -> [SExpr ()]
displayRest k ctx rest =
    displayOptional "precedes" (displayOrdering (orderings k))
     (displayOptional "non-orig" (displayTerms ctx (sansPts (knon k)))
      (displayOptional "pen-non-orig" (displayTerms ctx (sansPts (kpnon k)))
       (displayOptional "uniq-orig" (displayTerms ctx (sansPts (kunique k)))
        (displayOptional "gen-st" (displayTerms ctx (kgenSt k))
         (displayOptional "conf" (displayTerms ctx (kconf k))
          (displayOptional "auth" (displayTerms ctx (kauth k))
           (displayOptional "facts" (displayFacts ctx (kfacts k))
            -- (map (displayFact ctx) (kfacts
            -- k))            
             (displayOptional "priority" priorities
              (kcomment k ++
               (displayOptional "rule" (map (S ()) (krules k))
                (displayOperation k ctx
                 (displayOptional "traces" traces rest))))))))))))
    where
      priorities = map displayPriority (kpriority k)
      traces = map (L () . displayTrace ctx . trace) (insts k)

displayFacts :: Context -> [Fact] -> [SExpr ()]
displayFacts ctx =
    foldr
    (\(Fact name fs) soFar ->
         case name of
           "trans" -> soFar
           _ -> (L () (S () name : map (displayFterm ctx) fs)) : soFar)
    []

displayFact :: Context -> Fact -> SExpr ()
displayFact ctx (Fact name fs) =
  L () (S () name : map (displayFterm ctx) fs)

displayFterm :: Context -> FTerm -> SExpr ()
displayFterm _ (FSid s) = N () s
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
            maplets = L.sort (sansPtMaplets (reify domain (env s))) 
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
          displayCause
          (L () [S () "added-listener", displayOpCmt ctx $ CM $ Plain t]) cause
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
                displayOpCmt ctx critical :
                displayNode node :
                displayOpCmts ctx (S.toList escape)) : rest
      displayDirection Encryption = S () "encryption-test"
      displayDirection Nonce = S () "nonce-test"
      displayDirection Channel = S () "channel-test"
      displayMethod _ (Deleted node) =
          [S () "deleted", displayNode node]
      displayMethod _ (Weakened (n0, n1)) =
          [S () "weakened", L () [displayNode n0, displayNode n1] ]
      displayMethod ctx (Separated t) =
          [S () "separated", displayOpCmt ctx $ TM t]
      displayMethod ctx (Forgot t) =
          [S () "forgot", displayOpCmt ctx $ TM t]

-- Terms in the operation field may contain variables not in the skeleton
displayOpCmt :: Context -> CMT -> SExpr ()
displayOpCmt ctx cm = displayCmt (addToContext ctx $ cmtTerms cm) cm

displayOpCmts :: Context -> [CMT] -> [SExpr ()]
displayOpCmts ctx ts =
  map (displayCmt $ addToContext ctx ts') (L.sort ts)
  where
    ts' = concatMap cmtTerms ts

displayCmt :: Context -> CMT -> SExpr ()
displayCmt ctx (CM (Plain t)) = displayTerm ctx t
displayCmt ctx (CM (ChMsg ch t)) =
  L () [S () "ch-msg", displayTerm ctx ch, displayTerm ctx t]
displayCmt ctx (TM t) = displayTerm ctx t
