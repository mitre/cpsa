-- Loads protocols and preskeletons from S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Loader (loadSExprs) where

import Control.Monad

import qualified Data.List as L
import Data.Maybe (isJust)
import CPSA.Lib.Utilities
import CPSA.Lib.ReturnFail
import CPSA.Lib.SExpr
import CPSA.Signature (Sig, loadSig)
import CPSA.Algebra
import CPSA.Channel
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

loadSExprs :: MonadFail m => Sig -> String -> Gen -> [SExpr Pos] -> m [Preskel]
loadSExprs sig nom origin xs =
    do
      (_, ks) <- foldM (loadSExpr sig nom origin) ([], []) xs
      return (reverse ks)

loadSExpr :: MonadFail m => Sig -> String -> Gen -> ([Prot], [Preskel]) ->
             SExpr Pos -> m ([Prot], [Preskel])
loadSExpr sig nom origin (ps, ks) (L pos (S _ "defprotocol" : xs)) =
    do
      p <- loadProt sig nom origin pos xs
      return (p : ps, ks)
loadSExpr sig _ _ (ps, ks) (L pos (S _ "defskeleton" : xs)) =
    do
      k <- findPreskel sig pos ps xs
      return (ps, k : ks)
loadSExpr sig _ _ (ps, ks) (L pos (S _ "defgoal" : xs)) =
    do
      k <- findGoal sig pos ps xs
      return (ps, k : ks)
loadSExpr _ _ _ (ps, ks) (L _ (S _ "comment" : _)) = return (ps, ks)
loadSExpr _ _ _ (ps, ks) (L _ (S _ "herald" : _)) = return (ps, ks)
loadSExpr _ _ _ _ x = fail (shows (annotation x) "Malformed input")

-- load a protocol

loadProt :: MonadFail m => Sig -> String -> Gen -> Pos ->
            [SExpr Pos] -> m Prot
loadProt sig nom origin pos (S _ name : S _ alg : x : xs)
    | alg /= nom =
        fail (shows pos $ "Expecting terms in algebra " ++ nom)
    | otherwise =
        do
          sig <- loadLang pos sig xs
          (gen, rs, transRules, rest) <- loadRoles sig origin (x : xs)
          (gen', r) <- mkListenerRole sig pos gen
          let (gen,inits) = initRules sig gen' transRules
--             let (gen'', scissors) = scissorsRule gen'
--             let (gen''', cake) = cakeRule gen''
--             let (gen'''', intrpt) = uninterruptibleRule gen'''
--             let (genFive, shears) = shearsRule gen''''
--             let (gen, neqs) = neqRules genFive
--             let initRls = scissors : cake : intrpt : shears : (neqs ++ transRules)

          -- Fake protocol is used only for loading user defined rules
          let fakeProt = mkProt name alg gen sig rs r
                         inits
                         []     -- user-written rules
                         inits  -- loader-generated rules
                         []
          (gen, newRls, comment) <- loadRules sig fakeProt gen rest
          -- Check for duplicate role names
          (validate
           (mkProt name alg gen sig rs r
                       (newRls ++ (rules fakeProt))
                       newRls   -- user-written rules
                       (rules fakeProt) -- loader-generated rules
                       comment)
           rs)
    where
      validate prot [] = return prot
      validate prot (r : rs) =
          case L.find (\r' -> rname r == rname r') rs of
            Nothing -> validate prot rs
            Just _ ->
                let msg = "Duplicate role " ++ rname r ++
                          " in protocol " ++ name in
                fail (shows pos msg)
loadProt _ _ _ pos _ = fail (shows pos "Malformed protocol")

-- Optionally load a lang field in a protocol.
loadLang :: MonadFail m => Pos -> Sig -> [SExpr Pos] -> m Sig
loadLang pos _ xs | hasKey "lang" xs = loadSig pos (assoc "lang" xs)
loadLang _ sig _ | otherwise = return sig

loadRoles :: MonadFail m => Sig -> Gen -> [SExpr Pos] ->
             m (Gen, [Role], [Rule], [SExpr Pos])
loadRoles sig gen (L pos (S _ "defrole" : x) : xs) =
    do
      (gen, r, rls) <- loadRole sig gen pos x
      (gen, rs, rulesRest, comment) <- loadRoles sig gen xs
      return (gen, r : rs, (rls ++ rulesRest), comment)
loadRoles _ gen comment =
    return (gen, [], [], comment)

loadRole :: MonadFail m => Sig -> Gen -> Pos ->
            [SExpr Pos] -> m (Gen, Role, [Rule])
loadRole sig gen pos (S _ name :
                      L _ (S _ "vars" : vars) :
                      L _ (S _ "trace" : evt : c) :
                      rest) =
    do
      (gen, vars) <- loadVars sig gen vars
      (gen, vars, pt_u, c) <- -- indices computed below
          loadTrace sig gen vars (evt : c)
      n <- loadPosBaseTerms sig vars (assoc "non-orig" rest)
      a <- loadPosBaseTerms sig vars (assoc "pen-non-orig" rest)
      u <- loadBaseTerms sig vars (assoc "uniq-orig" rest)
      g <- loadBaseTerms sig vars (assoc "uniq-gen" rest)
      b <- mapM (loadAbsent sig vars) (assoc "absent" rest)
      d <- loadBaseTerms sig vars (assoc "conf" rest)
      h <- loadBaseTerms sig vars (assoc "auth" rest)
      cs <- loadCritSecs (assoc "critical-sections" rest)
      genstates <- loadTerms sig vars (assoc "gen-st" rest)
      facts <- loadFactList sig vars (assoc "facts" rest)

      let keys = ["non-orig", "pen-non-orig", "uniq-orig",
                  "uniq-gen", "absent", "conf", "auth"]
      comment <- alist keys rest
      let reverseSearch = hasKey "reverse-search" rest
      let ts = tterms c
      let bs = concatMap (\(x, y) -> [x, y]) b
      case termsWellFormed (map snd n ++ map snd a ++ u ++ g ++ bs ++ ts) of
        False -> fail (shows pos "Terms in role not well formed")
        True -> return ()
      case L.all isChan (d ++ h) of
        False -> fail (shows pos "Bad channel in role")
        True -> return ()
      -- Drop unused variable declarations
      let f v = elem v (varsInTerms ts) || elem v (tchans c)
      let vs = L.filter f vars
      -- Drop rnons that refer to unused variable declarations
      let ns = L.filter (varsSeen vs . snd) n
      -- Drop rpnons that refer to unused variable declarations
      let as = L.filter (varsSeen vs . snd) a
      -- Drop runiques that refer to unused variable declarations
      let us = L.filter (varsSeen vs) (u ++ pt_u)
      let gs = L.filter (varsSeen vs) g
      prios <- mapM (loadRolePriority (length c)) (assoc "priority" rest)

      let stateSegs = stateSegments c
      case all (flip checkCs stateSegs) cs of
        False -> fail (shows pos "Critical sections in role not within state segments")
        True -> return ()

      let r = mkRole name vs c ns as us gs b d h comment prios reverseSearch

      let (gen', transRls) = transRules sig gen r (transitionIndices c)
      -- :: Gen -> Role -> [Int] -> (Gen, [Rule])
      let (gen'', csRls) = csRules sig gen' r cs
      let (gen''', gsRls) = genStateRls sig gen'' r genstates
      let (genFour, factRls) = genFactRls sig gen''' r facts

      case roleWellFormed r of
        Return () -> return (genFour, r,
                             (factRls ++ gsRls ++ csRls ++ transRls))
        Fail msg -> fail (shows pos $ showString "Role not well formed: " msg)
loadRole _ _ pos _ = fail (shows pos "Malformed role")

loadRolePriority :: MonadFail m => Int -> SExpr Pos -> m (Int, Int)
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
roleWellFormed :: MonadFail m => Role -> m ()
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
      mapM_ uniqgenCheck $ runiqgen role
      mapM_ origVarCheck $ rvars role
      failwith "role trace is a prefix of a listener"
                   $ notListenerPrefix $ rtrace role
      failwith "role trace has stor with no previous load"
                   $ balancedStores $ rtrace role
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
      uniqgenCheck t =
          failwith (showString "uniq-gen " $ showst  t " doesn't generate")
                       $ generates t (rtrace role)
      origVarCheck v =
          failwith (showString "variable " $ showst v " not acquired")
                       $ not (isAcquiredVar v) ||
                         isJust (acquiredPos v (rtrace role))

--   noBareStore :: Trace -> Bool
--   noBareStore c =
--       check c Nothing
--       where
--         check [] _ = True
--         check ((In (ChMsg ch _)) : c') _
--             | isLocn ch              = check c' (Just ch)
--             | otherwise              = check c' Nothing
--         check ((Out (ChMsg ch _)) : c') (Just ch')
--             | ch == ch'              = check c' Nothing
--             | isLocn ch              = False
--             | otherwise              = check c' Nothing
--         check ((Out (ChMsg ch _)) : c') Nothing
--             | isLocn ch              = False
--             | otherwise              = check c' Nothing
--         check (_ : c') _             = check c' Nothing

balancedStores :: Trace -> Bool
balancedStores c =
    check c []
    where
      check [] _ = True
      check ((In (ChMsg ch _)) : c') loads
          | isLocn ch              = check c' (ch : loads)
          | otherwise              = check c' []
      check ((Out (ChMsg ch _)) : c') loads
          | ch `elem` loads         = check c' loads
          | isLocn ch              = False
          | otherwise              = check c' []
      check (_ : c') _             = check c' []

-- Given a trace, return a list of pairs of indices.  The first member
-- of each pair is the index of a state event.  If the state event is
-- a stor, then the second member is equal to the first.  If the state
-- event is a load, then there is a matching stor in the state
-- segment, and the second member is its index.

transitionIndices :: Trace -> [(Int, Int)]
transitionIndices c =
    reverse $ loop [] 0 c
    where
      loop so_far _ [] = so_far
      loop so_far i ((Out (ChMsg ch _)) : c')
           | isLocn ch              = loop ((i,i) : so_far) (i+1) c'
           | otherwise              = loop so_far (i+1) c'
      loop so_far i ((In (ChMsg ch _)) : c')
           | isLocn ch              =
               case subseqSend (i+1) ch c' of
                 Just j             -> loop ((i,j) : so_far) (i+1) c'
                 Nothing            -> loop so_far (i+1) c'
           | otherwise              = loop so_far (i+1) c'
      loop so_far i (_ : c')        = loop so_far (i+1) c'

      subseqSend _ _ []             = Nothing
      subseqSend j ch ((In (ChMsg _ _)) : c')
                                    = subseqSend (j+1) ch c'
      subseqSend j ch ((Out (ChMsg ch' _)) : c')
          | ch == ch'               = Just j
          | isLocn ch'              = subseqSend (j+1) ch c'
          | otherwise               = Nothing
      subseqSend _ _ (_ : _)        = Nothing

stateSegments :: Trace -> [(Int,Int)]
stateSegments c =
    findSegments [] 0 c
    where
      findSegments soFar _ [] = soFar
      findSegments soFar i ((Out _) : c) =
          findSegments soFar (i+1) c
      findSegments soFar i ((In (Plain _)) : c) =
          findSegments soFar (i+1) c
      findSegments soFar i ((In (ChMsg ch _)) : c)
          | isLocn ch           = findEnd soFar i (i+1) c False
          -- the flag False means that no Outs have yet been observed
          | otherwise            = findSegments soFar (i+1) c

      -- findEnd scans for the end of the segment starting at start.
      -- i is always the index of the start of c in the full trace.
      -- The boolean flag is False until Outs have been observed.

      findEnd soFar start i [] _                         = (start,(i-1)) : soFar

      findEnd soFar start i ((In (Plain _)) : c) _       =
          findSegments ((start,(i-1)) : soFar) (i+1) c
      findEnd soFar start i ((Out (Plain _)) : c) _      =
          findSegments ((start,(i-1)) : soFar) (i+1) c
      findEnd soFar start i c@((In (ChMsg _ _)) : _) True =
          findSegments ((start,(i-1)) : soFar)  i c
      -- in th eprevious case we save the start of c for findSegments
      -- to decide what to do.

      findEnd soFar start i ((In (ChMsg ch _)) : c) False
          | isLocn ch           = findEnd soFar start(i+1) c False
          | otherwise           = findSegments ((start,(i-1)) : soFar) (i+1) c
      findEnd soFar start i ((Out (ChMsg ch _)) : c) _
          | isLocn ch           = findEnd soFar start (i+1) c True
          | otherwise           = findSegments ((start,(i-1)) : soFar) (i+1) c

checkCs :: (Int,Int) -> [(Int,Int)] -> Bool
checkCs (i,j) =
    any
    (\(start,end) -> start <= i && j <= end)

{--
sepStateSegments :: Trace -> [(Int,Int,Int)]
sepStateSegments c =
    findSegments [] 0 c
    where
      findSegments soFar _ [] = soFar
      findSegments soFar i ((Out _) : c) =
          findSegments soFar (i+1) c
      findSegments soFar i ((In (Plain _)) : c) =
          findSegments soFar (i+1) c
      findSegments soFar i ((In (ChMsg ch _)) : c)
          | isLocn ch           = findMid soFar i (i+1) c
          -- the flag False means that no Outs have yet been observed
          | otherwise            = findSegments soFar (i+1) c

      -- findMid scans for the end of the load part of the segment
      -- segment starting at start.
      -- start is always the index of the start of c in the full trace.

      findMid soFar start i []                           = (start,(i-1),(i-1)) : soFar

      findMid soFar start i ((In (Plain _)) : c)         =
          findSegments ((start,(i-1),(i-1)) : soFar) (i+1) c
      findMid soFar start i ((Out (Plain _)) : c)        =
          findSegments ((start,(i-1),(i-1)) : soFar) (i+1) c

      findMid soFar start i ((In (ChMsg ch _)) : c)
          | isLocn ch           = findMid soFar start (i+1) c
          | otherwise           = findSegments ((start,(i-1),(i-1)) : soFar) (i+1) c

      findMid soFar start i ((Out (ChMsg ch _)) : c)
          | isLocn ch           = findEnd soFar start (i-1) (i+1) c
          | otherwise           = findSegments ((start,(i-1),(i-1)) : soFar) (i+1) c

      findEnd soFar start mid i [] = ((start,mid,(i-1)) : soFar)
      findEnd soFar start mid i ((Out (ChMsg ch _)) : c)
          | isLocn ch           = findEnd soFar start mid (i+1) c
          | otherwise           = findSegments ((start,mid,(i-1)) : soFar) (i+1) c

      findEnd soFar start mid i c@(_ : _) =
          findSegments ((start,mid,(i-1)) : soFar) i c
      -- in the previous case we save the start of c for findSegments
      -- to decide what to do.

--}

failwith :: MonadFail m => String -> Bool -> m ()
failwith msg test =
    case test of
      True -> return ()
      False -> fail msg

showst :: Term -> ShowS
showst t =
    shows $ displayTerm (addToContext emptyContext [t]) t

-- This is the only place a role is generated with an empty name.
-- This is what marks a strand as a listener.
mkListenerRole :: MonadFail m => Sig -> Pos -> Gen -> m (Gen, Role)
mkListenerRole sig pos g =
  do
    (g, xs) <- loadVars sig g [L pos [S pos "x", S pos "mesg"]]
    case xs of
      [x] -> return (g, mkRole "" [x] [In $ Plain x, Out $ Plain x]
                        [] [] [] [] [] [] [] [] [] False)
      _ -> fail (shows pos "mkListenerRole: expecting one variable")

-- Ensure a trace is not a prefix of a listener
notListenerPrefix :: Trace -> Bool
notListenerPrefix (In t : Out t' : _) | t == t' = False
notListenerPrefix _ = True

-- Protocol Rules

type VarListSpec = [(String,[String])]
type Conjunctor = [Term] -> [AForm] -- given universally bound vars,
                                    -- yields a conjunction
type Disjunctor = [Term] -> Conjunctor -- given existentially bound
                                       -- vars, yields a conjunctor

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

             --   loadFact :: MonadFail m => [Int] -> [Term] -> SExpr Pos -> m Fact
--   loadFact heights vars (L _ (S _ name : fs)) =
--     do
--       fs <- mapM (loadFterm heights vars) fs
--       return $ Fact name fs
--   loadFact _ _ x =
--     fail (shows (annotation x) "Malformed fact")
--
--   loadFterm :: MonadFail m => [Int] -> [Term] -> SExpr Pos -> m FTerm
--   loadFterm heights _ (N pos s)
--     | 0 <= s && s < length heights = return $ FSid s
--     | otherwise = fail (shows pos ("Bad strand in fact: " ++ show s))
--   loadFterm _ vars x =
--     do
--       t <- loadTerm vars x
--       return $ FTerm t
--

ruleOfClauses :: Sig -> Gen -> String ->
                 VarListSpec -> Conjunctor ->
                 [(VarListSpec,Disjunctor)] -> (Gen,Rule)
ruleOfClauses sig g rn sortedVarLists antecedent evarDisjs =
    let (g',uvars) = sortedVarsOfStrings sig g sortedVarLists in
    let (g'', disjs) =
            foldr
            (\(evarlist,djor) (g,disjs) ->
                 let (g',evars) = sortedVarsOfStrings sig g evarlist in
                 (g', (evars, (djor evars uvars)) : disjs))
            (g',[])
            evarDisjs in
    (g'',
      (Rule { rlname = rn,
              rlgoal =
                  (Goal
                   { uvars = uvars,
                     antec = antecedent uvars,
                     consq = disjs,
                     concl = map snd disjs}),
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
    L.foldl
     (\(g,rs) sortName ->
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

--   neqRules g =
--       L.foldl
--       (\(g, rs) sortName ->
--            let (g', v) = newVar g "x" sortName in
--            (g', ((Rule { rlname = "neqRule_" ++ sortName,
--                         rlgoal = Goal {uvars =  [v],
--                                        antec = [(AFact "neq" [v,v])],
--                                        consq = [],
--                                        concl = []},
--                         rlcomment = [] }) : rs)))
--       (g,[])
--       ["mesg", "strd", "indx"]

transRules :: Sig -> Gen -> Role -> [(Int,Int)] -> (Gen, [Rule])
transRules sig g rl =
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

--   (\(g, rs) idx ->
--             )
-- [(Trans (z,ti))]

--        let (g', z) = newVar g "z" "strd" in
--             let ti = (indxOfInt idx) in
--             (g', (Rule { rlname = ("transRule_" ++ (rname rl) ++
--                                    "-at-" ++ (show idx)),
--                          rlgoal = Goal {uvars =  [z],
--                                         antec = [(Length rl z (indxOfInt (idx+1)))],
--                                         consq = [([], -- no existentially
--                                                       -- bound vars
--                                                   [(Trans (z,ti))])],
--                                         concl = [[(Trans (z,ti))]]},
--                         rlcomment = [] }) : rs)

--   causeAndEffectIndices :: Role -> Int -> Int -> ([Int],[Int])
--   causeAndEffectIndices rl start end =
--       let c = drop start $ rtrace rl in
--       loopCause (start+1) [] c
--       where
--         loopCause _ causelist []          = (causelist,[])
--         loopCause i causelist ((In (ChMsg ch _)) : c)
--              | i < end && isLocn ch       = loopCause (i+1) (i : causelist) c
--              | otherwise                  = (causelist,[])
--         loopCause i causelist ((Out (ChMsg ch _)) : c)
--             | i <= end && isLocn ch       = loopEffect (z (i, end) i) causelist [i] c
--             | otherwise                  = (causelist,[])
--         loopCause _ causelist _          = (causelist,[])
--
--         loopEffect _ causelist effectlist []              = (causelist,effectlist)
--         loopEffect _ causelist effectlist ((In _) : _)    = (causelist,effectlist)
--         loopEffect i causelist effectlist ((Out (ChMsg ch _)) : c)
--             | i < (end-1) && isLocn ch   = loopEffect (i+1) causelist (i : effectlist) c
--             | otherwise                  = (causelist,effectlist)
--         loopEffect _ causelist effectlist ((Out _) : _)   = (causelist,effectlist)

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

      occ = flip firstOccurs rl

      heightLoop soFar [] = FoundAt (1+soFar)
      heightLoop soFar (v : rest) =
          case occ v of
            Nothing -> Missing v
            Just i -> heightLoop (max i soFar) rest

      vSpec t = ("strd", ["z"]) : varListSpecOfVars (varsInTerm t)

      f g t n =
          case heightLoop 0 (varsInTerm t) of
            Missing v -> error
                         ("genStateRls:  In gen-st of "
                          ++ (rname rl) ++ ": no occurrence of "
                                 ++ (show (displayTerm (addToContext emptyContext [t]) v)))
            FoundAt ht ->
                ruleOfClauses sig g
                  ("gen-st-" ++ (rname rl) ++ "-" ++ (show n))
                  (vSpec t)
                  (\vars ->
                       applyToStrandVarAndParams
                       (\z pvars ->
                            (Length rl z (indxOfInt ht))
                            : (map
                               (\v ->
                                    case paramOfName (varName v) rl of
                                      Nothing -> error ("genStateRls:  Parameter " ++
                                                        (varName v) ++ " not found.")
                                      Just p ->
                                          case firstOccurs p rl of
                                            Nothing -> error ("genStateRls:  Parameter " ++
                                                              (varName v) ++ " not found.")
                                            Just i -> (Param rl p (i+1) z v))
                              pvars))
                       vars
                       "genStateRls:  vars not strand+prams?")
                  [([],
                    (\_ vars ->
                         applyToStrandVarAndParams
                         (\_ pvars ->
                              case envsRoleParams rl g pvars of
                                [(_,e)] -> [GenStV (instantiate e t)]
                                _ -> error "genStateRls:  Non-unary matching not implemented")
                         vars
                         "genStateRls:  vars not strand+params?"))]

{-
genClaimRule :: Sig -> Gen -> Role -> [AForm] -> Int -> (Gen, Rule)
genClaimRule sig g rl aforms ht =
    case badvars of
      [] ->
          ruleOfClauses
          sig g ("claim-" ++ (rname rl) ++ "-" ++ (show ht))
           (vSpec params)
           (\vars ->
                applyToStrandVarAndParams
                (\z pvars ->
                     (Length rl z (indxOfInt ht))
                     : (map
                        (\v ->
                             case paramOfName (varName v) rl of
                               Nothing -> error ("genClaimRule:  Parameter " ++
                                                 (varName v) ++ " not found.")
                               Just p ->
                                   case firstOccurs p rl of
                                     Nothing -> error ("genClaimRule:  Parameter " ++
                                                       (varName v) ++ " not found.")
                                     Just i -> (Param rl p (i+1) z v))
                        pvars))
                vars
                "genClaimRule:  vars not strand+prams?")
           [([],
             (\_ vars ->
                  applyToStrandVarAndParams
                  (\_ pvars ->
                       case envsRoleParams rl g pvars of
                         [(_,e)] -> map (instantiateAForm e) aforms
                         _ -> error "genClaimRule:  Non-unary matching not implemented")
                  vars
                  "genClaimRule:  vars not strand+params?"))]
      b : rest -> error ("genClaimRule:  bad vars " ++ (show (b : rest)) ++ "occur too late")
    where
      tr = map evtTerm (rtrace rl)
      fvs = foldl aFreeVars [] aforms
      params = L.intersect (concatMap varsInTerm (take ht tr)) fvs
      badvars = L.intersect (concatMap varsInTerm (drop ht tr)) fvs
      evars = fvs L.\\ params
      vSpec args =
          (("strd", ["z"])
           : varListSpecOfVars (concatMap varsInTerm args))
-}

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

      occ = flip firstOccurs rl

      heightLoop soFar [] = Just (1+soFar)
      heightLoop soFar (v : rest) =
          case occ v of
            Nothing -> Nothing
            Just i -> heightLoop (max i soFar) rest

      vSpec args = ("strd", ["z"]) : varListSpecOfVars (varsInArgs args)

      varsInArgs = concatMap varsInTerm

      f g pred args n =
          case heightLoop 0 (varsInArgs args) of
            Nothing -> error ("genFactRls:  Unbound variable in fact of " ++
                             (rname rl) ++ ": " ++ pred ++ (show args))
            Just ht ->
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
                       "genFactRls:  vars not strand+prams?")
                  [([],
                    (\_ vars ->
                         applyToStrandVarAndParams
                         (\_ pvars ->
                              case envsRoleParams rl g pvars of
                                [(_,e)] -> [AFact pred (map (instantiate e) args)]
                                _ -> error "genFactRls:  Non-unary matching not implemented")
                         vars
                         "genFactRls:  vars not strand+params?"))]

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

initRules :: Sig -> Gen -> [Rule] -> (Gen, [Rule])
initRules sig g rs =
    let (g',neqs) = neqRules sig g in
    foldr (\f (g,rules) ->
               let (g',r) = f g in
               (g',r : rules))
    (g',neqs ++ rs)
    [scissorsRule sig, cakeRule sig, uninterruptibleRule sig,
     shearsRule sig, invShearsRule sig]

loadRules :: MonadFail m => Sig -> Prot -> Gen -> [SExpr Pos] ->
             m (Gen, [Rule], [SExpr ()])
loadRules sig prot g (L pos (S _ "defrule" : x) : xs) =
    do
      (g, r) <- loadRule sig prot g pos x
      (g, rs, comment) <- loadRules sig prot g xs
      return (g, r : rs, comment)
loadRules _ _ _ (L pos (S _ "defrole" : S _ name : _) : _) =
    fail (shows pos ("defrole " ++ name ++ " misplaced"))
loadRules _ _ g xs =
    do
      badKey ["defrole", "defrule"] xs
      comment <- alist [] xs    -- Ensure remaining is an alist
      return (g, [], comment)

loadRule :: MonadFail m => Sig -> Prot -> Gen -> Pos ->
            [SExpr Pos] -> m (Gen, Rule)
loadRule sig prot g pos (S _ name : x : xs) =
  do
    (g, goal, _) <- loadSentence sig UnusedVars pos prot g x
    comment <- alist [] xs      -- Ensure remaining is an alist
    return (g, Rule { rlname = name,
                      rlgoal = goal,
                      rlcomment = comment })
loadRule _ _ _ pos _ = fail (shows pos "Malformed rule")

-- Association lists

-- Make an association list into a comment.  The first argument is the
-- set of keys of key-value pairs to be dropped from the comment.

alist :: MonadFail m => [String] -> [SExpr Pos] -> m [SExpr ()]
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

-- Complain if alist has a bad key
badKey :: MonadFail m => [String] -> [SExpr Pos] -> m ()
badKey keys (L _ (S pos key : _) : xs)
    | elem key keys =
      fail (shows pos (key ++ " declaration too late in enclosing form"))
    | otherwise = badKey keys xs
badKey _ _ = return ()

loadTrace :: MonadFail m => Sig -> Gen -> [Term] ->
             [SExpr Pos] -> m (Gen, [Term], [Term], Trace)
loadTrace sig gen vars xs =
    loadTraceLoop gen [] [] [] xs
    where
      loadTraceLoop gen newVars uniqs events [] =
          return (gen, vars ++ (reverse newVars),
                  (reverse uniqs),
                  reverse events)
      loadTraceLoop gen newVars uniqs events ((L _ [S _ "recv", t]) : rest) =
          do
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs ((In $ Plain t) : events) rest
      loadTraceLoop gen newVars uniqs events ((L _ [S _ "send", t]) : rest) =
          do
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs ((Out $ Plain t) : events) rest
      loadTraceLoop gen newVars uniqs events ((L _ [S _ "recv", ch, t]) : rest) =
          do
            ch <- loadChan sig vars ch
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs ((In $ ChMsg ch t) : events) rest
      loadTraceLoop gen newVars uniqs events ((L _ [S _ "send", ch, t]) : rest) =
          do
            ch <- loadChan sig vars ch
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs ((Out $ ChMsg ch t) : events) rest
      loadTraceLoop gen newVars uniqs events ((L _ [S pos "load", ch, t]) : rest) =
          do
            ch <- loadLocn sig vars ch
            t <- loadTerm sig vars True t
            (gen, pt, pt_t) <- loadLocnTerm sig gen (S pos "pt") (S pos "pval") t
            loadTraceLoop gen (pt : newVars) uniqs
                              ((In $ ChMsg ch pt_t) : events) rest
--
--               (ch', trInds') <-
--                   (case rest of
--                      (L _ [S _ "stor", ch', _]) : _ ->
--                          (do
--                            ch' <- loadLocn vars ch'
--                            return (ch', (i : trInds)))
--                      _ -> return (ch, trInds))
--               case ch == ch' of
--                      False -> fail (shows pos ("distinct locns in load/stor pair"))
--                      True -> loadTraceLoop gen (pt : newVars) uniqs
--                              ((In $ ChMsg ch pt_t) : events) trInds' (i+1) rest
      loadTraceLoop gen newVars uniqs events ((L _ [S pos "stor", ch, t]) : rest) =
          do
            ch <- loadLocn sig vars ch
            t <- loadTerm sig vars True t
            (gen, pt, pt_t) <- loadLocnTerm sig gen (S pos "pt") (S pos "pval") t
            loadTraceLoop gen (pt : newVars) (pt : uniqs)
                              ((Out $ ChMsg ch pt_t) : events) rest

      loadTraceLoop _ _ _ _ ((L pos [S _ dir, _, _]) : _) =
          fail (shows pos $ "Unrecognized direction " ++ dir)
      loadTraceLoop _ _ _ _ (x : _) =
          fail (shows (annotation x) "Malformed event")

loadChan :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadChan sig vars x =
  do
    ch <- loadTerm sig vars True x
    case isChan ch || isLocn ch of
      True -> return ch
      False -> fail (shows (annotation x) "Expecting a channel or location")

loadLocn :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadLocn sig vars x =
  do
    ch <- loadTerm sig vars True x
    case isLocn ch of
      True -> return ch
      False -> fail (shows (annotation x) "Expecting a location")

loadBaseTerms :: MonadFail m => Sig -> [Term] -> [SExpr Pos] -> m [Term]
loadBaseTerms _ _ [] = return []
loadBaseTerms sig vars (x : xs) =
    do
      t <- loadBaseTerm sig vars x
      ts <- loadBaseTerms sig vars xs
      return (adjoin t ts)

loadBaseTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadBaseTerm sig vars x =
    do
      t <- loadTerm sig vars True x
      case isAtom t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an atom")

loadPosBaseTerms :: MonadFail m => Sig -> [Term] -> [SExpr Pos] ->
                    m [(Maybe Int, Term)]
loadPosBaseTerms _ _ [] = return []
loadPosBaseTerms sig vars (x : xs) =
    do
      t <- loadPosBaseTerm sig vars x
      ts <- loadPosBaseTerms sig vars xs
      return (t:ts)

loadPosBaseTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos ->
                   m (Maybe Int, Term)
loadPosBaseTerm sig vars x'@(L _ [N _ opos, x])
    | opos < 0 =
        fail (shows (annotation x')
              "Expecting a non-negative non-origination position")
    | otherwise =
        do
          t <- loadBaseTerm sig vars x
          return (Just opos, t)
loadPosBaseTerm sig vars x =
    do
      t <- loadTerm sig vars True x
      case isAtom t of
        True -> return (Nothing, t)
        False -> fail (shows (annotation x) "Expecting an atom")

loadAbsent :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m (Term, Term)
loadAbsent sig vars (L _ [x, y]) =
    do
      x <- loadVarExprTerm sig vars x
      y <- loadExprTerm sig vars y
      return (x, y)
loadAbsent _ _ x =
    fail (shows (annotation x) "Expecting a pair of terms")

loadExprTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadExprTerm sig vars x =
    do
      t <- loadTerm sig vars False x
      case isExpr t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an exponent")

loadVarExprTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadVarExprTerm sig vars x =
    do
      t <- loadTerm sig vars True x
      case isVarExpr t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an exponent variable")

-- Find protocol and then load a preskeleton.

findPreskel :: MonadFail m => Sig -> Pos -> [Prot] ->
               [SExpr Pos] -> m Preskel
findPreskel sig pos ps (S _ name : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> loadPreskel sig pos p xs
findPreskel _ pos _ _ = fail (shows pos "Malformed skeleton")

loadPreskel :: MonadFail m => Sig -> Pos -> Prot -> [SExpr Pos] -> m Preskel
loadPreskel sig pos p (L _ (S _ "vars" : vars) : xs) =
    do
      (gen, kvars) <- loadVars sig (pgen p) vars
      loadInsts sig pos p kvars gen [] xs
loadPreskel _ pos _ _ = fail (shows pos "Malformed skeleton")

loadInsts :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> Gen ->
             [Instance] -> [SExpr Pos] -> m Preskel
loadInsts sig top p kvars gen insts (L pos (S _ "defstrand" : x) : xs) =
    case x of
      S _ role : N _ height : env ->
          do
            (gen, i) <- loadInst sig pos p kvars gen role height env
            loadInsts sig top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrand")
loadInsts sig top p kvars gen insts (L pos (S _ "deflistener" : x) : xs) =
    case x of
      [term] ->
          do
            (gen, i) <- loadListener sig p kvars gen term
            loadInsts sig top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed deflistener")
loadInsts sig top p kvars gen insts xs =
    do
      badKey ["defstrand", "deflistener"] xs
      _ <- alist [] xs          -- Check syntax of xs
      (gen, gs) <- loadGoals sig top p gen goals
      loadRest sig top kvars p gen gs (reverse insts)
        order nr ar ur ug ab pr cn au fs pl genSts kcomment
    where
      order = assoc "precedes" xs
      nr = assoc "non-orig" xs
      ar = assoc "pen-non-orig" xs
      ur = assoc "uniq-orig" xs
      ug = assoc "uniq-gen" xs
      ab = assoc "absent" xs
      pr = assoc "precur" xs
      cn = assoc "conf" xs
      au = assoc "auth" xs
      fs = assoc "facts" xs
      pl = assoc "priority" xs
      goals = assoc "goals" xs
      genSts = assoc "gen-st" xs
      kcomment =
        loadComment "goals" goals ++
        loadComment "comment" (assoc "comment" xs)

loadComment :: String -> [SExpr Pos] -> [SExpr ()]
loadComment _ [] = []
loadComment key comment =
  [L () (S () key : map strip comment)]

loadInst :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> Gen -> String ->
            Int -> [SExpr Pos] -> m (Gen, Instance)
loadInst sig pos p kvars gen role height env =
    do
      r <- lookupRole pos p role
      case height < 1 || height > length (rtrace r) of
        True -> fail (shows pos "Bad height")
        False ->
            do
              let vars = rvars r
              (gen', env') <- foldM (loadMaplet sig kvars vars)
                              (gen, emptyEnv) env
              return (mkInstance gen' r env' height)

lookupRole :: MonadFail m => Pos -> Prot -> String -> m Role
lookupRole _ p role  | role == "" =
    return $ listenerRole p
lookupRole pos p role =
    case L.find (\r -> role == rname r) (roles p) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname p)
      Just r -> return r

loadMaplet :: MonadFail m => Sig -> [Term] -> [Term] ->
              (Gen, Env) -> SExpr Pos -> m (Gen, Env)
loadMaplet sig kvars vars env (L pos [domain, range]) =
    do
      t <- loadTerm sig vars False domain
      t' <- loadTerm sig kvars False range
      case match t t' env of
        env' : _ -> return env'
        [] -> fail (shows pos "Domain does not match range")
loadMaplet _ _ _ _ x = fail (shows (annotation x) "Malformed maplet")

loadListener :: MonadFail m => Sig -> Prot -> [Term] -> Gen -> SExpr Pos ->
                m (Gen, Instance)
loadListener sig p kvars gen x =
    do
     t <- loadTerm sig kvars True x
     return $ mkListener p gen t

loadRest :: MonadFail m => Sig -> Pos -> [Term] -> Prot -> Gen -> [Goal] ->
            [Instance] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] ->
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr ()] -> m Preskel
loadRest sig pos vars p gen gs insts orderings
         nr ar ur ug ab pr cn au fs pl genSts comment =
    do
      case null insts of
        True -> fail (shows pos "No strands")
        False -> return ()
      let heights = map height insts
      o <- loadOrderings heights orderings
      nr <- loadBaseTerms sig vars nr
      ar <- loadBaseTerms sig vars ar
      ur <- loadBaseTerms sig vars ur
      ug <- loadBaseTerms sig vars ug
      ab <- mapM (loadAbsent sig vars) ab
      pr <- mapM (loadNode heights) pr
      cn <- loadBaseTerms sig vars cn
      au <- loadBaseTerms sig vars au
      fs <- mapM (loadFact sig heights vars) fs
      genSts <- mapM (loadTerm sig vars True) genSts
      let (nr', ar', ur', ug', ab', cn', au') =
            foldl addInstOrigs (nr, ar, ur, ug, ab, cn, au) insts
      prios <- mapM (loadPriorities heights) pl
      let k = mkPreskel gen p gs insts o nr' ar' ur'
              ug' ab' pr genSts cn' au' fs prios comment
          ab'' = L.concatMap (\(x, y) -> [x, y]) ab'
      case termsWellFormed $ nr' ++ ar' ++ ur' ++ ug' ++ ab'' ++ kterms k of
        False -> fail (shows pos "Terms in skeleton not well formed")
        True -> return ()
      case L.all isChan (cn' ++ au') of
        False -> fail (shows pos "Bad channel in role")
        True -> return ()
      case verbosePreskelWellFormed k of
        Return () -> return k
        Fail msg -> fail $ shows pos
                    $ showString "Skeleton not well formed: " msg

loadOrderings :: MonadFail m => [Int] -> [SExpr Pos] -> m [Pair]
loadOrderings heights x =
    foldM f [] x
    where
      f ns x =
          do
            np <- loadPair heights x
            return (adjoin np ns)

loadPair :: MonadFail m => [Int] -> SExpr Pos -> m Pair
loadPair heights (L pos [x0, x1]) =
    do
      n0 <- loadNode heights x0
      n1 <- loadNode heights x1
      case fst n0 == fst n1 of  -- Same strand
        True -> fail (shows pos "Malformed pair -- nodes in same strand")
        False -> return (n0, n1)
loadPair _ x = fail (shows (annotation x) "Malformed pair")

loadNode :: MonadFail m => [Int] -> SExpr Pos -> m Node
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

loadFact :: MonadFail m => Sig -> [Int] -> [Term] -> SExpr Pos -> m Fact
loadFact sig heights vars (L _ (S _ name : fs)) =
  do
    fs <- mapM (loadFterm sig heights vars) fs
    return $ Fact name fs
loadFact _ _ _ x =
  fail (shows (annotation x) "Malformed fact")

loadFterm :: MonadFail m => Sig -> [Int] -> [Term] -> SExpr Pos -> m FTerm
loadFterm _ heights _ (N pos s)
  | 0 <= s && s < length heights = return $ FSid s
  | otherwise = fail (shows pos ("Bad strand in fact: " ++ show s))
loadFterm sig _ vars x =
  do
    t <- loadTerm sig vars True x
    return $ FTerm t

loadPriorities :: MonadFail m => [Int] -> SExpr Pos -> m (Node, Int)
loadPriorities heights (L _ [x, N _ p]) =
    do
      n <- loadNode heights x
      return (n, p)
loadPriorities _ x =
    fail (shows (annotation x) "Malformed priority")

addInstOrigs :: ([Term], [Term], [Term], [Term], [(Term, Term)], [Term], [Term])
                -> Instance ->
                ([Term], [Term], [Term], [Term], [(Term, Term)], [Term], [Term])
addInstOrigs (nr, ar, ur, ug, ab, cn, au) i =
    (foldl (flip adjoin) nr $ inheritRnon i,
     foldl (flip adjoin) ar $ inheritRpnon i,
     foldl (flip adjoin) ur $ inheritRunique i,
     foldl (flip adjoin) ug $ inheritRuniqgen i,
     foldl (flip adjoin) ab $ inheritRabsent i,
     foldl (flip adjoin) cn $ inheritRconf i,
     foldl (flip adjoin) au $ inheritRauth i)

-- Security goals

-- Load a defgoal form
findGoal :: MonadFail m => Sig -> Pos -> [Prot] -> [SExpr Pos] -> m Preskel
findGoal sig pos ps (S _ name : x : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p ->
        do
          (g, goal, antec) <- loadSentence sig RoleSpec pos p (pgen p) x
          let (gs, xs') = findAlist xs
          (g, goals) <- loadGoals sig pos p g gs
          _ <- alist [] xs'          -- Check syntax of xs
          let kcomment =
                loadComment "goals" (x : gs) ++
                loadComment "comment" (assoc "comment" xs')
          -- Make and return the characteristic skeleton of a security goal
          characteristic pos p (goal : goals) g antec kcomment
findGoal _ pos _ _ = fail (shows pos "Malformed goal")

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

loadGoals :: MonadFail m => Sig -> Pos -> Prot -> Gen ->
             [SExpr Pos] -> m (Gen, [Goal])
loadGoals _ _ _ g [] = return (g, [])
loadGoals sig pos prot g (x : xs) =
  do
    (g, goal, _) <- loadSentence sig RoleSpec pos prot g x
    (g, goals) <- loadGoals sig pos prot g xs
    return (g, goal : goals)

data Mode
  = RoleSpec
  | UnusedVars

-- Load a single security goal, a universally quantified formula
-- Returns the goal and the antecedent with position information.

loadSentence :: MonadFail m => Sig -> Mode -> Pos -> Prot -> Gen ->
                SExpr Pos -> m (Gen, Goal, Conj)
loadSentence sig md _ prot g (L pos [S _ "forall", L _ vs, x]) =
  do
    (g, vars) <- loadVars sig g vs
    loadImplication sig md pos prot g vars x
loadSentence _ _ pos _ _ _ = fail (shows pos "Bad goal sentence")

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
          UnusedVars pos prot (evars ++ vars) evars x
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

-- Load a conjuction of atomic formulas and ensure that all declared
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

-- Load a conjunction of atomic formulas

loadConjunction :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                   SExpr Pos -> m Conj
loadConjunction sig _ p kvars (L pos (S _ "and" : xs)) =
  loadConjuncts sig pos p kvars xs []
loadConjunction sig top p kvars x =
  do
    (pos, a) <- loadPrimary sig top p kvars x
    return [(pos, a)]

loadConjuncts :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
                 [SExpr Pos] -> Conj -> m Conj
loadConjuncts _ _ _ _ [] rest = return (reverse rest)
loadConjuncts sig top p kvars (x : xs) rest =
  do
    (pos, a) <- loadPrimary sig top p kvars x
    loadConjuncts sig top p kvars xs ((pos, a) : rest)

-- Load the atomic formulas

loadPrimary :: MonadFail m => Sig -> Pos -> Prot -> [Term] ->
               SExpr Pos -> m (Pos, AForm)
loadPrimary sig _ _ kvars (L pos [S _ "=", x, y]) =
  do
    t <- loadTerm sig kvars True x
    t' <- loadTerm sig kvars True y
    case isStrdVar t == isStrdVar t' of
      True -> return (pos, Equals t t')
      False -> fail (shows pos "Sort mismatch in equality")
loadPrimary sig _ _ kvars (L pos [S _ "component", x, y]) =
  do
    t <- loadTerm sig kvars True x
    t' <- loadTerm sig kvars True y
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
    fs <- mapM (loadTerm sig kvars True) fs
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
    h <- loadTerm sig kvars True ht
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

loadCritSecs :: MonadFail m => [SExpr Pos] -> m [(Int, Int)]
loadCritSecs [] = return []
loadCritSecs (L pos [(N _ i), (N _ j)] : rest)
    | j<i = fail (shows pos "loadCritSecs:  Bad int pair out of order")
    | otherwise =
        do
          pairs <- loadCritSecs rest
          return ((i,j) : pairs)
loadCritSecs s = fail ("loadCritSecs:  Malformed int pairs: " ++ (show s))

-- Load a term and make sure it does not have sort strd, indx, locn, or chan

loadAlgTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadAlgTerm sig ts x =
  do
    t <- loadTerm sig ts True x
    case isStrdVar t || isIndxVar t || isIndxConst t || isChan t || isLocn t of
      True -> fail (shows (annotation x) "Expecting an algebra term")
      False -> return t
-- Load a term and make sure it does not have sort strd, or indx

loadAlgChanTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadAlgChanTerm sig ts x =
  do
    t <- loadTerm sig ts True x
    case isStrdVar t || isIndxVar t || isIndxConst t of
      True -> fail (shows (annotation x)
                    "Expecting an algebra term or a channel")
      False -> return t

-- Load a term and make sure it has sort chan

loadChanTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadChanTerm sig ts x =
  do
    t <- loadTerm sig ts True x
    case isChan t of
      True -> return t
      False -> fail (shows (annotation x) "Expecting a channel variable")

-- Load a term and make sure it has sort strd

loadStrdTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadStrdTerm sig ts x =
  do
    t <- loadTerm sig ts True x
    case isStrdVar t of
      True -> return t
      False -> fail (shows (annotation x) "Expecting a strand variable")

-- Load a term and make sure it has sort indx

loadIndxTerm :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadIndxTerm sig ts x =
  do
    t <- loadTerm sig ts True x
    case isIndxVar t of
      True -> return t
      False ->
        case isIndxConst t of
          True -> return t
          False -> fail (shows (annotation x) "Expecting an indx variable")

-- Load a term and make sure it describes a node

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
