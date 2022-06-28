-- Generates rules when loading protocols from S-Expressions.  

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.GenRules where

import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Signature (Sig)
import CPSA.Algebra
import CPSA.Channel
import CPSA.Protocol
import CPSA.LoadFormulas
-- Protocol Rules

type Conjunction = [AForm]

conjunctionOfConj :: Conj -> Conjunction
conjunctionOfConj = map snd 

type Conjunctor = [Term] -> Conjunction -- Function which, given new
                                        -- free variables, plugs them
                                        -- in to yield a conjunction

type Existor = [Term] -> Conjunctor     -- Function which, given new
                                        -- variables to bind
                                        -- existentially, plugs them
                                        -- in to yield a conjunctor

    
{-- 
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
--}
                  



ruleOfClauses :: Sig -> Gen -> String ->
                 VarListSpec -> Conjunctor ->
                 [(VarListSpec,Existor)] -> (Gen,Rule)
ruleOfClauses sig g rn sortedVarLists antecedent evarDisjuncts =
    let (g',uvars) = sortedVarsOfStrings sig g sortedVarLists in
    let (g'', disjuncts) =
            foldr
            (\(evarlist,existor) (g,disjs) ->
                 let (g',evars) = sortedVarsOfStrings sig g evarlist in
                 (g', (evars, (existor evars
                               -- use only the members
                                -- of uvars that avoid names in evars 
                               (avoidByName evars uvars))) :
                  disjs))
            (g',[])
            evarDisjuncts in
    (g'',
      (Rule { rlname = rn,
              rlgoal =
                  (Goal
                   { uvars = uvars,
                     antec = antecedent uvars,
                     consq = disjuncts,
                     concl = map snd disjuncts}),
              rlcomment = [] }))
    where
      varOfName _ [] = Nothing
      varOfName name (v : rest) =
          if (name == varName v)
          then Just v
          else varOfName name rest
          
      avoidByName evars uvars =
          map (\uv ->
                   case varOfName (varName uv) evars of
                     Nothing -> uv
                     Just ev -> ev)                          
          uvars 

applyToSoleEntry :: (a -> b) ->  String -> [a] -> b
applyToSoleEntry f _ [a] = f a
applyToSoleEntry _ s _ = error s

applyToThreeEntries :: (a -> a -> a -> b) -> String -> [a] -> b
applyToThreeEntries f _ [a1,a2,a3] = f a1 a2 a3
applyToThreeEntries _ s _ = error s

applyToStrandVarAndParams :: (a -> [a] -> b) -> [a] -> String -> b
applyToStrandVarAndParams _ [] s = error s
applyToStrandVarAndParams f (a : rest) _ = f a rest

-- foldM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b

neqRules :: Sig -> Gen -> (Gen, [Rule])
neqRules sig g =
    foldr  
     (\sortName (g,rs) ->
          let (g', r) =
                  (ruleOfClauses sig g ("neqRl_" ++ sortName)
                   [(sortName,["x"])]
                   (applyToSoleEntry
                    (\x -> [(AFact "neq" [x,x])])
                    "neqrules:  Impossible var list.")
                   [])       -- false conclusion
          in
          (g', r : rs))
     (g,[])
     ["indx", "strd", "mesg"]

transRls :: Sig -> Gen -> Role -> [(Int,Int)] -> (Gen, [Rule])
transRls sig g rl =
    L.foldl
     (\(g, rs) pair ->
          let (g', r) = f g pair in
          (g', r : rs))
     (g, [])
     where
       f g (i,j) =
           ruleOfClauses sig g ("trRl_" ++ (rname rl) ++ "-at-" ++ (show i))
             [("strd",["z"])]
             (applyToSoleEntry
              (\z -> [(Length rl z (indxOfInt (j+1)))])
              "transRules:  Impossible var list.")
             [([],                   -- no existentially bound vars
               (\_ -> applyToSoleEntry
                        (\z -> [(Trans (z, (indxOfInt i)))])
                        "transRules:  Impossible var list."))]

lastRecvInCS :: Role -> Int -> Int -> Int
lastRecvInCS rl start end =
    loop start $ drop (start+1) $ rtrace rl
    -- i is always the index before the index of the first entry still
    -- in c.
    where
      loop i ((In (ChMsg ch _)) : c)
           | i < end && isLocn ch       = loop (i+1) c
           | otherwise                  = i
      loop i _                          = i

csRules :: Sig -> Gen -> Role -> [(Int,Int)] -> (Gen, [Rule])
csRules sig g rl =
    L.foldl
     (\(g, rs) (start,end) ->
          (let (g', csRules) = f g start end in
           (g', csRules ++ rs)))
     (g,[])
     where
       f g start end =
           let lastRecv = lastRecvInCS rl start end in
           let (g',rs) = foldr (\ind (g,soFar) ->
                                    let (g',r) = causeRule g rl start ind in
                                    (g', (r : soFar)))
                         (g,[])
                         [start+1..lastRecv] in
           foldr (\ind (g,soFar) ->
                      let (g',r) = effectRule g rl end ind in
                      (g', (r : soFar)))
             (g',rs)
             [lastRecv+1..end-1]

       causeRule g rl start ind =
           ruleOfClauses sig g
             ("cau-" ++ (rname rl) ++ "-" ++ (show ind))
             [("strd",["z", "z1"]), ("indx", ["i"])]
             (applyToThreeEntries
              (\z z1 i -> [(Length rl z (indxOfInt (ind+1))),
                           (Prec -- LeadsTo
                            (z1,i) (z,(indxOfInt ind)))])
                      "csRules:  Impossible var list.")
             [([],
               (\_ -> applyToThreeEntries
                      (\z z1 _ -> [Equals z z1])
                      "csRules:  Impossible var list.")),
              ([],
               (\_ -> applyToThreeEntries
                      (\z z1 i -> [(Prec (z1,i) (z,(indxOfInt start)))])
                      "csRules:  Impossible var list."))]

       effectRule g rl end ind =
           ruleOfClauses sig g
             ("eff-" ++ (rname rl) ++ "-" ++ (show ind))
             [("strd",["z", "z1"]), ("indx", ["i"])]
             (applyToThreeEntries
              (\z z1 i -> [(Length rl z (indxOfInt (ind+1))),
                           (Prec --LeadsTo
                            (z, (indxOfInt ind)) (z1,i))])
              "csRules:  Impossible var list.")
             [([],
               (\_ -> applyToThreeEntries
                      (\z z1 _ -> [Equals z z1])
                      "csRules:  Impossible var list.")),
              ([],
               (\_ -> applyToThreeEntries
                      (\z z1 i -> [(Length rl z (indxOfInt (end+1))),
                                   (Prec (z, (indxOfInt end)) (z1,i))])
                "csRules:  Impossible var list."))]

data FoundAt = FoundAt Int
             | Missing Term

varsUsedHeight :: Role -> [Term] -> FoundAt
varsUsedHeight rl vars =
    loop 0 vars
    where
      occ = flip firstOccurs rl
      loop i [] = FoundAt (1+i)
      loop i (v : rest) =
          case occ v of
            Nothing -> Missing v
            Just j -> loop (max i j) rest

boundVarNamesOfVarListSpec :: VarListSpec -> [String]
boundVarNamesOfVarListSpec [] = []
boundVarNamesOfVarListSpec ((_,names) : rest) =
    L.nub $ names ++ boundVarNamesOfVarListSpec rest

freeVarsInExistential :: (VarListSpec,Existor) -> [Term]
freeVarsInExistential (vspec,c) = 
    let bvns = boundVarNamesOfVarListSpec vspec in
    concatMap
    (\a -> filter (not . (flip elem bvns) . varName)
           (aFreeVars [] a))
    (c [] [])

freeVarsInDisjunction :: [(VarListSpec,Existor)] -> [Term]
freeVarsInDisjunction vcs =
    L.nub
     (foldr (\vc acc -> (freeVarsInExistential vc) ++ acc) 
      []
      vcs)

renameApart :: String -> [VarListSpec] -> String
renameApart prefix vspecs =
    if not (prefix `elem` vns) then prefix
    else
        loop 0 
    where
      vns = concatMap boundVarNamesOfVarListSpec vspecs      
      loop :: Int -> String
      loop i =
          let candidate = prefix ++ "-" ++ (show i) in
          if not (candidate `elem` vns) then candidate
          else
              loop (i+1) 

ruleOfDisjAtHeight :: Sig -> Gen -> Role -> String -> [(VarListSpec,Existor)] -> Int -> (Gen, Rule)
ruleOfDisjAtHeight sig g rl rulename disj ht =
    let fvs = freeVarsInDisjunction disj in 
    ruleOfClauses
    sig g rulename 
            (("strd", [renameApart "z" (map fst disj)]) : varListSpecOfVars fvs)
            (\vars ->
                 applyToStrandVarAndParams
                 (\z pvars ->
                      (Length rl z (indxOfInt ht))
                      : (map
                         (\v ->
                              case paramOfName (varName v) rl of
                                Nothing -> errorWithMsg v " not found."
                                Just p ->
                                    case firstOccurs p rl of
                                      Nothing -> errorWithMsg v " not found."
                                      Just i ->
                                          if i < ht then (Param rl p (i+1) z v)
                                          else errorWithMsg v " introduced too high.")
                         pvars))
                 vars
                 "ruleOfDisjAtHeight:  vars not strand+prams?")
            disj                

            --   (map
--                (\(vspec,conj) ->
--                     (vspec,
--                      (\evars uvars -> 
--   
--                           
--                      (\_ vars ->
--                           let bvarnames = boundVarNamesOfVarListSpec vspec in 
--                           applyToStrandVarAndParams
--                            (\_ pvars ->
--                                 case envsRoleParams rl g bvarnames pvars of
--                                   (_,e) : _ -> instantiateConj e conj
--                                   _ -> errorWithMsg (L.head pvars) "Parameter matching failed:  Huh?")
--                            vars
--                            "ruleOfDisjAtHeight:  vars not strand+params?"))))
--                disj)

    where
      errorWithMsg v tail =
          error ("ruleOfDisjAtHeight:  Parameter " ++
                 (varName v) ++ tail)
                  


genStateRls :: Sig -> Gen -> Role -> [Term] -> (Gen, [Rule])
genStateRls sig g rl ts =
    (g',rls)
    where
      (g',rls,_) =
          foldr (\t (g, rs, n) ->
                       (let (g', new_rule) = f g t n in
                        (g', new_rule : rs, n+1)))
               (g, [], (0 :: Integer))
               ts      

      -- vSpec t = ("strd", ["z"]) : varListSpecOfVars (varsInTerm t)

      f g t n =
          case varsUsedHeight rl (varsInTerm t) of
            Missing v ->
                error ("genStateRls:  In gen-st of "
                       ++ (rname rl) ++ ": no occurrence of "
                              ++ (show (displayTerm (addToContext emptyContext [t]) v)))
            FoundAt ht ->
                (ruleOfDisjAtHeight
                 sig g rl ("gen-st-" ++ (rname rl) ++ "-" ++ (show n))
                 [ -- One disjunct, no existentially bound variables
                   ([], 
                   -- One conjunctor:  
                    (\_ pvars ->
                          case envsRoleParams rl g pvars of
                            (_,e) : _ -> [GenStV (instantiate e t)] 
                            _ -> error ("genStateRls:  Parameter matching failed "
                                        ++  (show pvars) ++ (show t))))]
                 ht)

genFactRls :: Sig -> Gen -> Role -> [(String,[Term])] -> (Gen, [Rule])
genFactRls sig g rl predarglists =
        (g',rls)
    where
      (g',rls,_) =
          foldr (\(pred,args) (g, rs, n) ->
                     (let (g', new_rule) = f g pred args n in
                      (g', new_rule : rs, n+1)))
                    (g, [], (0 :: Integer))
                    predarglists      

      -- vSpec t = ("strd", ["z"]) : varListSpecOfVars (varsInTerm t) 

      f g pred args n =
          case varsUsedHeight rl (concatMap varsInTerm args) of
            Missing v ->
                error ("genFactRls:  In fact of "
                       ++ (rname rl) ++ ": no occurrence of "
                              ++ (show $ varName v))
            FoundAt ht ->
                (ruleOfDisjAtHeight
                 sig g rl ("fact-" ++ (rname rl) ++ "-" ++ pred ++ (show n))                         
                 [ -- One disjunct, no existentially bound variables
                   ([], 
                   -- One conjunctor:  
                    (\_ pvars ->
                         case envsRoleParams rl g pvars of
                           (_,e) : _ ->  [AFact pred (map (instantiate e) args)]
                           _ -> error ("genFactRls:  Parameter matching failed "
                                       ++  (show pvars) ++ (concatMap show args))))]
                 ht)

      {-- 
    (g',rls)
    where
      (g',rls,_) =
          foldr (\(pred,args) (g, rs, n) ->
                       (let (g', new_rule) = f g pred args n in
                        (g', new_rule : rs, n+1)))
               (g, [], (0 :: Integer))
               predarglists

      vSpec args = ("strd", ["z"]) : varListSpecOfVars (varsInArgs args)

      varsInArgs = concatMap varsInTerm

      f g pred args n =
          case varsUsedHeight rl (varsInArgs args) of
            Missing v -> error ("genFactRls:  Unbound variable " ++ (show v)
                               ++ " in fact of " ++ (rname rl) ++ ": "
                               ++ pred ++ (show args))
            FoundAt ht ->
                ruleOfClauses sig g
                  ("fact-" ++ (rname rl) ++ "-" ++ pred ++ (show n))
                  (vSpec args)
                  (\vars ->
                       applyToStrandVarAndParams
                       (\z pvars ->
                            (Length rl z (indxOfInt ht))
                            : (map
                               (\v ->
                                    case paramOfName (varName v) rl of
                                      Nothing -> error ("genFactRls:  Parameter " ++
                                                        (varName v) ++ " not found.")
                                      Just p ->
                                          case firstOccurs p rl of
                                            Nothing -> error ("genFactRls:  Parameter " ++
                                                              (varName v) ++ " not found.")
                                            Just i -> (Param rl p (i+1) z v))
                              pvars))
                       vars
                       "genFactRls:  vars not strand+params?")
                  [([],
                    (\_ vars ->
                         applyToStrandVarAndParams
                         (\_ pvars ->
                              case envsRoleParams rl g [] pvars of
                                [(_,e)] -> [AFact pred (map (instantiate e) args)]
                                _ -> error "genFactRls:  Non-unary matching not implemented")
                         vars
                         "genFactRls:  vars not strand+params?"))]
--}

theVacuousRule :: Rule
theVacuousRule =
    (Rule { rlname = "vacuity",
            rlgoal = Goal {uvars =  [],
                           antec = [],
                           consq = [([], [])], -- no bvs, no conjuncts
                           concl = [[]]},
            rlcomment = [] })

scissorsRule :: Sig -> Gen -> (Gen, Rule)
scissorsRule sig g =
    case sortedVarsOfNames sig g "strd" ["z0","z1","z2"] of
      (g, [z0,z1,z2]) ->
          case sortedVarsOfNames sig g "indx" ["i0","i1","i2"] of
            (g, [i0,i1,i2]) ->
                (g, (Rule { rlname = "scissorsRule",
                        rlgoal =
                            Goal
                            {uvars = [z0,z1,z2,i0,i1,i2],
                             antec = [ -- useful for debugging:
                                       -- (AFact "no-state-split" []),
                                       (Trans (z0,i0)), (Trans (z1,i1)), (Trans (z2,i2)),
                                       (LeadsTo (z0,i0) (z1,i1)), (LeadsTo (z0,i0) (z2,i2)) ],
                             consq = [([],                -- no bvs
                                       [(Equals z1 z2),   -- two eqns
                                        (Equals i1 i2)])],
                             concl = [[(Equals z1 z2),   -- two eqns
                                       (Equals i1 i2)]]},
                        rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

shearsRule :: Sig -> Gen -> (Gen, Rule)
shearsRule sig g =
    case sortedVarsOfNames sig g "strd" ["z0","z1","z2"] of
      (g, [z0,z1,z2]) ->
          case sortedVarsOfNames sig g "indx" ["i0","i1","i2"] of
            (g, [i0,i1,i2]) ->
                (g, (Rule { rlname = "shearsRule",
                        rlgoal =
                            Goal
                            {uvars = [z0,z1,z2,i0,i1,i2],
                             antec = [ -- useful for debugging:
                                       -- (AFact "no-state-split" []),
                                       (Trans (z0,i0)), (Trans (z1,i1)), (Trans (z2,i2)),
                                       (LeadsTo (z0,i0) (z1,i1)), (SameLocn (z0,i0) (z2,i2)),
                                       (Prec (z0,i0) (z2,i2)) ],
                             consq = [([],                -- no bvs
                                       [(Equals z1 z2),   -- two eqns
                                        (Equals i1 i2)]),
                                     ([],                -- no bvs
                                      -- (z1,i1) precedes (z2,i2)
                                       [(Prec (z1, i1) (z2, i2))])],
                             concl = [[(Equals z1 z2),   -- two eqns
                                        (Equals i1 i2)],
                                      -- (z1,i1) precedes (z2,i2)
                                       [(Prec (z1, i1) (z2, i2))]]},
                        rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

invShearsRule :: Sig -> Gen -> (Gen, Rule)
invShearsRule sig g =
    case sortedVarsOfNames sig g "strd" ["z0","z1","z2"] of
      (g, [z0,z1,z2]) ->
          case sortedVarsOfNames sig g "indx" ["i0","i1","i2"] of
            (g, [i0,i1,i2]) ->
                (g, (Rule { rlname = "invShearsRule",
                        rlgoal =
                            Goal
                            {uvars = [z0,z1,z2,i0,i1,i2],
                             antec = [ -- useful for debugging:
                                       -- (AFact "no-state-split" []),
                                       (Trans (z0,i0)), (Trans (z1,i1)),
                                       (SameLocn (z0,i0) (z1,i1)),
                                       (LeadsTo (z1,i1) (z2,i2)), (Prec (z0,i0) (z2,i2)) ],
                             consq = [([],                -- no bvs
                                       [(Equals z0 z1),   -- two eqns
                                        (Equals i0 i1)]),
                                     ([],                -- no bvs
                                      -- (z0, i0) precedes (z1,i1)
                                       [(Prec (z0, i0) (z1, i1))])],
                             concl = [[(Equals z0 z1),   -- two eqns
                                        (Equals i0 i1)],
                                      -- (z0, i0) precedes (z1,i1)
                                       [(Prec (z0, i0) (z1, i1))]]},
                        rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

uninterruptibleRule :: Sig -> Gen -> (Gen, Rule)
uninterruptibleRule sig g =
    case sortedVarsOfNames sig g "strd" ["z0","z1","z2"] of
      (g, [z0,z1,z2]) ->
          case sortedVarsOfNames sig g "indx" ["i0","i1","i2"] of
            (g, [i0,i1,i2]) ->
                (g,
                 (Rule { rlname = "no-interruption",
                         rlgoal =
                             Goal
                             {uvars = [z0,z1,z2,i0,i1,i2],
                              antec = [ (LeadsTo (z0,i0) (z2,i2)), (Trans (z1,i1)),
                                        (SameLocn (z0,i0) (z1,i1)), (Prec (z0,i0) (z1,i1)),
                                        (Prec (z1,i1) (z2,i2)) ],
                              consq = [], -- implies False
                              concl = []},
                         rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

cakeRule :: Sig -> Gen -> (Gen, Rule)
cakeRule sig g =
    case sortedVarsOfNames sig g "strd" ["z0","z1","z2"] of
      (g, [z0,z1,z2]) ->
          case sortedVarsOfNames sig g "indx" ["i0","i1","i2"] of
            (g, [i0,i1,i2]) ->
                (g,
                 (Rule { rlname = "cakeRule",
                         rlgoal =
                             Goal
                             {uvars = [z0,z1,z2,i0,i1,i2],
                              antec = [ (Trans (z0,i0)), (Trans (z1,i1)),
                                        (LeadsTo (z0,i0) (z1,i1)), (LeadsTo (z0,i0) (z2,i2)),
                                        (Prec (z1,i1) (z2,i2)) ],
                              consq = [], -- implies False
                              concl = []},
                         rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)
