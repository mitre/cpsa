
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

-- a Renamer is a function that will replace variables within the
-- AForm that should be regarded as universally bound with the
-- variable that will be chosen for the universal quantifier.

-- The loader will in fact read these variables as occurrences of the
-- role parameters
type Renamer = AForm -> AForm

type Conjunctor = Conjunction -> Renamer -> Conjunction
-- Function which, given Conjunction and a fn to plug in new
-- variables, plugs them in to yield a conjunction

-- The loader ensures that when an existential formula's body is
-- loaded, anything that can be read as a local, existentially bound
-- variable will be.  Since these are generated immediately before the
-- body is read, there can be no occurrences of the role parameters
-- present in the body.  Likewise, there can be no occurrences of the
-- local, existentially bound variables outside this body.

-- Hence a renamer for the antecedent may be safely applied here,
-- without capturing variables that should be locally bound.

type Existor = Conjunctor

-- Used to say:   -- Function which, given new
                                        -- variables to bind
                                        -- existentially, plugs them
                                        -- in to yield a conjunctor

ruleOfClauses :: Sig -> Gen -> String ->
                 [Term] ->  -- VarListSpec ->
                 Conjunction ->
                 [([Term],Conjunction)] -> (Gen,Rule)
ruleOfClauses _ g rn fvs antecedent evarDisjuncts = -- sig is vacuous
    let (g', env, uvars) = renamerAndNewVars fvs g in
    let disjuncts =
            map
            (\(evars,c) -> (evars,
                            (map (instantiateAForm env) c)))
            evarDisjuncts in
    (g',
      (Rule { rlname = rn,
              rlgoal =
                  (Goal
                   { uvars = uvars,
                     antec = map (instantiateAForm env) antecedent,
                     consq = disjuncts,
                     concl = map snd disjuncts}),
              rlcomment = [] }))

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
          let (g', v) = newVar sig g "x" sortName in
          let (g'', r) =
                  (ruleOfClauses sig g' ("neqRl_" ++ sortName)
                   [v]
                   [(AFact "neq" [v,v])]
                   [])       -- false conclusion
          in
            (g'', r : rs))
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
           let (g', z) = newVar sig g "z" "strd" in
           ruleOfClauses sig g' ("trRl_" ++ (rname rl) ++ "-at-" ++ (show i))
             [z]
             [(Length rl z (indxOfInt (j+1)))]
             [                  --one disjunct
              ([],              -- no existentially bound vars
               [(Trans (z, (indxOfInt i)))] -- one conjunct
               )]

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
       f g start end = stateSegStrRule g rl start end
       -- let lastRecv = lastRecvInCS rl start end in
--              if start == end then (g,[])
--              else 
--                  let (g',rc) = causeRule g rl start end in
--                  let (g'',re) = effectRule g' rl end start in
--                  let (g''',rf) = fullCSRule g'' rl start end in
--                  (g''', [rf, rc, re])


       stateSegStrRule g rl start end =
           let (g',z) = newVar sig g "z" "strd" in
           
           -- (a -> b -> b) -> b -> t a -> b
           foldr
           (\j (g'',soFar) ->
            let (g''',r) = (ruleOfClauses sig g''
                            ("st-sg-" ++ (rname rl) ++ "-" ++ (show j))
                            [z]
                            [(Length rl z (indxOfInt (j+1)))]
                            [([],
                              [AFact "st-sg-str"
                               [z, (indxOfInt start), (indxOfInt j)]])]) in
            (g''', r : soFar))
           (g',[])
           [start+1..end]
           

{--            

       causeRule g rl start ind =
           let (g',z) = newVar sig g "z" "strd" in
           let (g'', z1) = newVar sig g' "z1" "strd" in
           let (g''', i) = newVar sig g'' "i" "indx" in

           ruleOfClauses sig g'''
             ("cau-" ++ (rname rl) ++ "-" ++ (show ind))
             [z, z1, i]
             [(Length rl z (indxOfInt (ind+1))),
              (Prec (z1,i) (z, (indxOfInt ind)))]

             [([],              -- either z = z1
               [Equals z z1]),
              ([],              -- or z1's i node comes before start
                                -- of critical section
               [(Prec (z1,i) (z,(indxOfInt start)))])]

       effectRule g rl end ind =
           let (g',z) = newVar sig g "z" "strd" in
           let (g'', z1) = newVar sig g' "z1" "strd" in
           let (g''', i) = newVar sig g'' "i" "indx" in

           ruleOfClauses sig g'''
             ("eff-" ++ (rname rl) ++ "-" ++ (show ind))
             [z, z1, i]
             [(Length rl z (indxOfInt (ind+1))),
              (Prec (z, (indxOfInt ind)) (z1,i))]
             [([],              -- either z = z1
               [Equals z z1]),
              ([],              -- or z is long and z1's i node comes
                                -- after end of critical section
               [(Length rl z (indxOfInt (end+1))),
                (Prec (z, (indxOfInt end)) (z1,i))])]

       fullCSRule g rl start end =
           let (g',z) = newVar sig g "z" "strd" in
           (ruleOfClauses sig g'
            ("full-cs-" ++ (rname rl) ++ "-" ++ (show start))
            [z]
            [(Length rl z (indxOfInt (start+1)))]
            [([], 
              [(Length rl z (indxOfInt (end+1)))])])
--}

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

{--
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
--}

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

{-

Sig -> Gen -> String -> [Term] ->
Conjunction -> [([Term],Conjunction)] -> (Gen,Rule)

--}

ruleOfDisjAtHeight :: Sig -> Gen -> Role -> String -> [([Term],[AForm])] -> Int -> (Gen, Rule)
ruleOfDisjAtHeight sig g rl rulename disj ht =
    let fvs = fvsConsq disj in
    let rvs = L.filter (\t -> L.elem t (rvars rl)) fvs in
    let (g',z) = newVar sig g "z" "strd" in
    (ruleOfClauses
     sig g' rulename
     (fvs ++ [z])
     ((Length rl z (indxOfInt ht)) :
      (map
       (\v ->
            case firstOccurs v rl of
              Nothing -> errorWithMsg v " not found."
              Just i ->
                  if i < ht
                  then (Param rl v (i+1) z v)
                  else errorWithMsg v
                           (" introduced for " ++ (varName v) ++ " too high in role " ++
                            (rname rl) ++": " ++ (show i) ++
                            " not below " ++ (show ht) ++ "in " ++ rulename ++ "."))
       rvs))
     disj)
    where
      errorWithMsg v tail =
          error ("ruleOfDisjAtHeight:  Parameter " ++
                 (varName v) ++ tail)

genOneAssumeRl :: Sig -> Gen -> Role -> Int -> [([Term], Conj)] -> (Gen, Rule)
genOneAssumeRl sig g rl n disjs =
    case conclHeight rl disjs of
      Missing v -> error ("genOneAssumeRl:  Variable not in role " ++ (rname rl)
                         ++ ": " ++ (show v))
      FoundAt ht ->
          let disjuncts = map (\(vs,cs) -> (vs, map snd cs)) disjs in
          ruleOfDisjAtHeight
          sig g rl ("assume-" ++ (rname rl) ++ "-" ++ (show n))
              disjuncts
              ht

genAssumeRls :: Sig -> Gen -> Role -> [[([Term], Conj)]] -> (Gen, [Rule])
genAssumeRls sig g rl disjs =
    (g',rls)
    where
      (g',rls,_) =
          foldr (\ds (g, rs, n) ->
                       (let (g', new_rule) = genOneAssumeRl sig g rl n ds in
                        (g', new_rule : rs, n+1)))
               (g, [], (0 :: Int))
               disjs

genOneRelyGuarRl :: Sig -> Gen -> Role -> Int -> String -> [([Term], Conj)] -> (Gen, Rule)
genOneRelyGuarRl sig g rl ht kind disjs =
    case conclHeight rl disjs of
      Missing v -> error ("genOneRelyGuarRl:  Variable not in role " ++ (rname rl)
                         ++ ": " ++ (show (varName v)))
      FoundAt fndHt
          | fndHt <= ht ->
              let disjuncts = map (\(vs,cs) -> (vs, map snd cs)) disjs in
              (ruleOfDisjAtHeight
               sig g rl (kind ++ "-" ++ (rname rl) ++ "-" ++ (show ht))
               disjuncts ht)
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
                   -- One conjunct:
                    [GenStV t])]
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
                   -- One conjunct:
                    [AFact pred args])]
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
                (g, (Rule { rlname = "discreteAfter",
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
                (g, (Rule { rlname = "discreteBefore",
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


causeRule :: Sig -> Gen -> (Gen, Rule)
causeRule sig g =
    case sortedVarsOfNames sig g "strd" ["z","z1"] of
      (g, [z,z1]) ->
          case sortedVarsOfNames sig g "indx" ["i","j","i1"] of
            (g, [i,j,i1]) ->
                (g,
                 (Rule { rlname = "causeRule",
                         rlgoal =
                             Goal
                             {uvars = [z,z1, i,j,i1],
                              antec = [ (AFact "st-sg-str" [z,i,j]),
                                        (Prec (z1,i1) (z,j)) ],
                              consq = [([], [Equals z z1]),
                                       ([], [Prec (z1,i1) (z,i)]) ], -- disjunction 
                              concl = [[Equals z z1],
                                       [Prec (z1,i1) (z,i)]]},
                         rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

                                
effectRule :: Sig -> Gen -> (Gen, Rule)
effectRule sig g =
    case sortedVarsOfNames sig g "strd" ["z","z1"] of
      (g, [z,z1]) ->
          case sortedVarsOfNames sig g "indx" ["i","j","i1"] of
            (g, [i,j,i1]) ->
                (g,
                 (Rule { rlname = "effectRule",
                         rlgoal =
                             Goal
                             {uvars = [z,z1, i,j,i1],
                              antec = [ (AFact "st-sg-str" [z,i,j]),
                                        (Prec (z,i) (z1,i1)) ],
                              consq = [([], [Equals z z1]),
                                       ([], [Prec (z,j) (z1,i1)]) ], -- disjunction 
                              concl = [[Equals z z1],
                                       [Prec (z,j) (z1,i1)]]},
                         rlcomment = [] }))
            (g, _) -> (g, theVacuousRule)
      (g, _) -> (g, theVacuousRule)

                                
