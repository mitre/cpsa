
-- Generates rules when loading protocols from S-Expressions.  

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.GenRules where

import qualified Data.List as L
-- import CPSA.Lib.SExpr
import CPSA.Signature (Sig)
import CPSA.Algebra
import CPSA.Channel
import CPSA.Protocol
import CPSA.LoadFormulas

{--
import System.IO.Unsafe

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x

zb :: Show a => a -> Bool -> Bool
zb a False = z a False
zb _ b = b

zn :: Show a => a -> Maybe b -> Maybe b
zn x Nothing = z x Nothing
zn _ y = y

zf :: Show a => a -> Bool -> Bool
zf x False = z x False
zf _ y = y

zt :: Show a => a -> Bool -> Bool
zt x True = z x True
zt _ y = y

zl :: Show a => [a] -> [a]
zl a = z (length a) a

--}


    
-- Protocol Rules

type Conjunction = [AForm]

conjunctionOfConj :: Conj -> Conjunction
conjunctionOfConj = map snd 

type Conjunctor = [Term] -> Conjunction -- Function which, given new
                                        -- free variables, plugs them
                                        -- in to yield a conjunction
-- [Term] -> 
type Existor = Conjunctor

-- Used to say:   -- Function which, given new
                                        -- variables to bind
                                        -- existentially, plugs them
                                        -- in to yield a conjunctor


 

ruleOfClauses :: Sig -> Gen -> String ->
                 VarListSpec -> Conjunctor ->
                 [([Term],Existor)] -> (Gen,Rule)
ruleOfClauses sig g rn sortedVarLists antecedent evarDisjuncts =
    let (g',uvars) = sortedVarsOfStrings sig g sortedVarLists in
    let disjuncts =
            map 
            (\(evars,existor) ->
                 (evars,(existor -- evars
                          -- use only the members
                          -- of uvars that avoid names in evars 
                         (avoidByName evars uvars))))
            evarDisjuncts in
    (g',
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
               (applyToSoleEntry
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
               (applyToThreeEntries
                (\z z1 _ -> [Equals z z1])
                "csRules:  Impossible var list.")),
              ([],
               (applyToThreeEntries
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
               (applyToThreeEntries
                (\z z1 _ -> [Equals z z1])
                "csRules:  Impossible var list.")),
              ([],
               (applyToThreeEntries
                (\z z1 i -> [(Length rl z (indxOfInt (end+1))),
                             (Prec (z, (indxOfInt end)) (z1,i))])
                "csRules:  Impossible var list."))]

data FoundAt = FoundAt Int
             | Missing Term

-- Return the smallest height in the trace of rl at which all of the
-- vars are found to have occurred, if found, or a missing var if no
-- such height.
varsUsedHeight :: Role -> [Term] -> FoundAt
varsUsedHeight rl vars =
    loop 0 vars
    where
      occ = flip firstOccurs rl -- return *index* 
      loop i [] = FoundAt (1+i) -- convert to height 
      loop i (v : rest) =
          case occ v of
            Nothing -> Missing v
            Just j -> loop (max i j) rest


boundVarNamesOfVarListSpec :: VarListSpec -> [String]
boundVarNamesOfVarListSpec [] = []
boundVarNamesOfVarListSpec ((_,names) : rest) =
    L.nub $ names ++ boundVarNamesOfVarListSpec rest

freeVarsInExistential :: ([Term],Existor) -> [Term]
freeVarsInExistential (vars,c) = 
    let bvns = map varName vars in
    concatMap
    (\a -> filter (not . (flip elem bvns) . varName)
           (aFreeVars [] a))
    (c [])

freeVarsInDisjunction :: [([Term],Existor)] -> [Term]
freeVarsInDisjunction vcs =
    L.nub
     (foldr (\vc acc -> (freeVarsInExistential vc) ++ acc) 
      []
      vcs)

freeVarsInConjLists :: [([Term], Conj)] -> [Term]
freeVarsInConjLists [] = []
freeVarsInConjLists ((vars,conj) : rest) =    
    ((foldr (\(_,aForm) soFar -> aFreeVars soFar aForm)
                []
                conj)
     L.\\ vars)
    ++ (freeVarsInConjLists rest)

-- Take the subset of fvars that have a name shared with some member
-- of pvars
freeVarsSubsetByName :: [Term] -> [Term] -> [Term]
freeVarsSubsetByName fvars pvars =
    loop fvars []
    where
      pvarNames = map varName pvars
      loop [] soFar = reverse soFar
      loop (fv : rest) soFar
          | (varName fv) `elem` pvarNames =
              loop rest (fv : soFar)
          | otherwise =
              loop rest soFar
          
--   freeVarsNamedIn [] pvars = []
--   freeVarsNamedIn (fv : rest) pvars =
--       if (varName fv) `elem` (map varName pvars)
--       then fv : freeVarsNamedIn rest pvars
--       else freeVarsNamedIn rest pvars

conclHeight :: Role -> [([Term], Conj)] -> FoundAt
conclHeight _ [] = FoundAt 1
conclHeight rl (disj : rest) =
    case conclHeight rl rest of
      Missing v -> Missing v
      FoundAt j ->
          case varsUsedHeight rl $ freeVarsInConjLists [disj] of
            Missing v -> Missing v
            FoundAt i -> FoundAt (max i j)
    

renameApart :: String -> [Term] -> String
renameApart prefix vars =
    if not (prefix `elem` vns) then prefix
    else
        loop 0 
    where
      vns = map varName vars
      loop :: Int -> String
      loop i =
          let candidate = prefix ++ "-" ++ (show i) in
          if not (candidate `elem` vns) then candidate
          else
              loop (i+1)

                   

ruleOfDisjAtHeight :: Sig -> Gen -> Role -> String -> [([Term],Existor)] -> Int -> (Gen, Rule)
ruleOfDisjAtHeight sig g rl rulename disj ht =
    let fvs = freeVarsInDisjunction disj in 
    ruleOfClauses
    sig g rulename 
            (("strd", [renameApart "z" (concatMap fst disj)])
             : varListSpecOfVars (freeVarsSubsetByName fvs (rvars rl)))
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
                                          else errorWithMsg v
                                                   (" introduced for " ++ (varName p) ++ " too high in role " ++ (rname rl) ++": " ++ (show i) ++
                                                    " not below " ++ (show ht) ++ "in " ++ rulename ++ "."))
                         pvars))
                 vars
                 "ruleOfDisjAtHeight:  vars not strand+prams?")
            disj
            
    where
      errorWithMsg v tail =
          error ("ruleOfDisjAtHeight:  Parameter " ++
                 (varName v) ++ tail)

genOneAssumeRl :: Sig -> Gen -> Role -> Int -> [([Term], Conj)] -> (Gen, Rule)
genOneAssumeRl sig g rl n disjuncts =
    case conclHeight rl disjuncts of
      Missing v -> error ("genOneAssumeRl:  Variable not in role " ++ (rname rl) 
                         ++ ": " ++ (show (varName v)))
      FoundAt ht -> 
          ruleOfDisjAtHeight
          sig g rl ("assume-" ++ (rname rl) ++ "-" ++ (show n))
                  (map (\(evars,conj) ->
                            (evars,
                             (\pvars ->
                              case envsRoleParams rl g pvars of
                                (_,e) : _ -> (map snd $ instantiateConj e conj)
                                _ -> error ("genOneAssumeRl:  Parameter matching failed "
                                            ++  (show pvars) ++ (rname rl)))))
                   disjuncts)
                  ht

--   
--       where
--         freeVars bndList conjunct = (aFreeVars [] conjunct) L.\\ bndList
--   
--         vars = L.nub (concatMap (\(vars,conj) ->
--                                      concatMap (freeVars vars) (map snd conj))
--                       disjuncts)
    
genAssumeRls :: Sig -> Gen -> Role -> [[([Term], Conj)]] -> (Gen, [Rule])
genAssumeRls sig g rl disjunctLists =
    (g',rls)
    where
      (g',rls,_) =
          foldr (\ds (g, rs, n) ->
                       (let (g', new_rule) = genOneAssumeRl sig g rl n ds in
                        (g', new_rule : rs, n+1)))
               (g, [], (0 :: Int))
               disjunctLists  


genOneRelyGuarRl :: Sig -> Gen -> Role -> Int -> String -> [([Term], Conj)] -> (Gen, Rule)
genOneRelyGuarRl sig g rl ht kind disjuncts =
    case conclHeight rl disjuncts of
      Missing v -> error ("genOneRelyGuarRl:  Variable not in role " ++ (rname rl) 
                         ++ ": " ++ (show (varName v)))
      FoundAt fndHt | fndHt <= ht -> 
          ruleOfDisjAtHeight
          sig g rl (kind ++ "-" ++ (rname rl) ++ "-" ++ (show ht))
                  (map (\(evars,conj) ->
                            (evars,
                             (\pvars ->
                              case envsRoleParams rl g pvars of
                                (_,e) : _ -> (map snd $ instantiateConj e conj)
                                _ -> error ("genOneAssumeRl:  Parameter matching failed "
                                            ++  (show pvars) ++ (rname rl)))))
                   disjuncts)
                  ht
        | otherwise -> error ("genOneRelyGuarRl:  Variable found above ht " ++ (show ht) ++
                              " in " ++ (rname rl))


genStateRls :: Sig -> Gen -> Role -> [Term] -> (Gen, [Rule])
genStateRls sig g rl ts =
    (g',rls)
    where
      (g',rls,_) =
          foldr (\t (g, rs, n) ->
                       (let (g', new_rule) = f g t n in
                        (g', new_rule : rs, n+1)))
               (g, [], (0 :: Int))
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
                    (\pvars ->
                         case envsRoleParams rl g pvars of
                           (_,e) : _ -> [GenStV (instantiate e t)] 
                           [] -> error ("genStateRls:  Parameter matching failed "
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
                    (g, [], (0 :: Int))
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
                    (\pvars ->
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
