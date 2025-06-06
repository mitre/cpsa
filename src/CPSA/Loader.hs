-- Loads protocols and preskeletons from S-expressions.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Loader (loadSExprs) where

import Control.Monad

import qualified Data.List as L
import qualified Data.Foldable as F
import Data.Maybe (isJust)
import CPSA.Lib.Utilities
import CPSA.Lib.ReturnFail
import CPSA.Lib.SExpr
import CPSA.Signature (Sig, loadSig)
import CPSA.Algebra
import CPSA.Channel
import CPSA.Protocol
import CPSA.Operation
import CPSA.Strand
import CPSA.Characteristic
import CPSA.LoadFormulas
import CPSA.GenRules

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
loadSExpr _ _ _ (ps, ks) (L pos (S _ "defskeleton" : xs)) =
    do
      k <- findPreskel pos ps xs
      return (ps, k : ks)
loadSExpr _ _ _ (ps, ks) (L pos (S _ "defgoal" : xs)) =
    do
      k <- findGoal pos ps xs
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
          (gen, rolesAndPreRules, rest) <- loadRoles sig origin (x : xs)
          (gen, r) <- mkListenerRole sig pos gen
          let rs = map fst rolesAndPreRules

          -- let _ = zz (showRoleGenStates rolesAndPreRules)

          -- let (gen, rls) = initRules sig (any hasLocn rs) gen' stateRules nonStateRules

          -- Fake protocol is used only for loading user defined rules
          let fakeProt = mkProt name alg gen sig rs r
                         []     -- was rls
                         []     -- user-written rules
                         []   -- loader-generated rules was rls
                         []

          (gen, forgettableRls, memorableRls) <- initRules sig gen fakeProt rolesAndPreRules

          (gen, newRls, comment) <- loadRules sig fakeProt gen rest
          -- Check for duplicate role names
          (validate
           (mkProt name alg gen sig rs r
                       (newRls ++ forgettableRls ++ memorableRls)
                       (newRls ++ memorableRls)  -- user-written rules
                       forgettableRls -- loader-regenerated rules
                       comment)
           rs)
    where
      validate prot [] =
          case checkForDivergenceInStoreSegments prot of
            Nothing -> return prot
            Just (name, name', i) ->
                fail ("checkForDivergenceInStoreSegments:  Roles " ++ name ++
                        " and " ++ name' ++ " agree up to step " ++ (show i) ++
                        " but diverge in a store segment.  " ++ 
                        " Distinguish them prior to second event in store segment")

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
             m (Gen, [(Role,PreRules)], [SExpr Pos])
loadRoles sig gen (L pos (S _ "defrole" : x) : xs) =
    do
      (gen, r, pr) <- loadRole sig gen pos x
      (gen, rolesAndPreRules, comment) <- loadRoles sig gen xs
      return (gen, (r,pr) : rolesAndPreRules, comment)
loadRoles _ gen comment =
    return (gen, [], comment)

loadRole :: MonadFail m => Sig -> Gen -> Pos ->
            [SExpr Pos] -> m (Gen, Role, PreRules)
loadRole sig gen pos (S _ name :
                      L _ (S _ "vars" : vars) :
                      L _ (S _ "trace" : evt : c) :
                      rest) =
    do
      (gen, vars) <- loadVars sig gen vars
      (gen, vars, pt_u, pr_t, c) <-
          -- critical section indices computed below
          loadTrace sig gen vars (evt : c)
      n <- loadPosBaseTerms sig vars (assoc "non-orig" rest)
      a <- loadPosBaseTerms sig vars (assoc "pen-non-orig" rest)
      u <- loadBaseTerms sig vars (assoc "uniq-orig" rest)
      g <- loadBaseTerms sig vars (assoc "uniq-gen" rest)
      b <- mapM (loadAbsent sig vars) (assoc "absent" rest)
      d <- loadBaseTerms sig vars (assoc "conf" rest)
      h <- loadBaseTerms sig vars (assoc "auth" rest)
      cs <- loadCritSecs (assoc "critical-sections" rest)
      let genstates = (assoc "gen-st" rest)
      let facts = (assoc "facts" rest)
      let assumes = (assoc "assume" rest)

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
    {-- case all (flip checkCs stateSegs) cs of
      False -> fail (shows pos "Critical sections in role not within state segments")
      True -> return () --}

      case cs of
        [] -> return ()
        _ -> fail (shows pos ("Critical sections in role are no longer needed;  " ++
                              "all state segments are now critical sections"))

      let r = mkRole name vs c ns as us gs b d h comment prios reverseSearch

      let pr = pr_t { preruleCs = stateSegs,
                      preruleTrans = transitionIndices c,
                      preruleFacts = facts,
                      preruleGensts = genstates,
                      preruleAssumes = assumes }

--         let (gen', transRls) = transRules sig gen r (transitionIndices c)
--         -- :: Gen -> Role -> [Int] -> (Gen, [Rule])
--         let (gen'', csRls) = csRules sig gen' r cs
--         let (gen''', gsRls) = genStateRls sig gen'' r genstates
--         let (genFour, factRls) = genFactRls sig gen''' r facts

      case roleWellFormed r of
        Return () -> return (gen, r, pr
                           --  (gsRls ++ csRls ++ transRls),
                           --  factRls
                            )
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

data PreRules = PreRules { preruleCs      :: [(Int,Int)],
                           preruleTrans   :: [(Int,Int)],
                           preruleFacts   :: [SExpr Pos],
                           preruleGensts  :: [SExpr Pos],
                           preruleAssumes :: [SExpr Pos],
                           preruleRelies  :: [(Int, SExpr Pos)],
                           preruleGuars   :: [(Int, SExpr Pos)],
                           preruleCheqs   :: [(Int, Pos, Term, Term)]
                         }

emptyPreRules :: PreRules
emptyPreRules = PreRules { preruleCs = [],
                           preruleTrans = [],
                           preruleFacts = [],
                           preruleGensts = [],
                           preruleAssumes = [],
                           preruleRelies  = [],
                           preruleGuars  = [],
                           preruleCheqs = []}

preRulesAddRely :: PreRules -> (Int, SExpr Pos) -> PreRules
preRulesAddRely pr new = pr { preruleRelies = new : preruleRelies pr }

preRulesAddGuar :: PreRules -> (Int, SExpr Pos) -> PreRules
preRulesAddGuar pr new = pr { preruleGuars = new : preruleGuars pr }

preRulesAddCheq :: PreRules -> (Int, Pos, Term, Term) -> PreRules
preRulesAddCheq pr new = pr { preruleCheqs = new : preruleCheqs pr }

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
      mapM_ (checkChanDecl "conf") $ rconf role
      mapM_ (checkChanDecl "auth") $ rauth role 
      failwith "role trace is a prefix of a listener"
                   $ notListenerPrefix $ rtrace role
      -- 
      -- Let's try obliterating the requirement that stored locns must
      -- previously have been loaded!
      --                     
      --         failwith "role trace has stor with no previous load"
      --                      $ balancedStores $ rtrace role
      -- 
      failwith "role trace has multiple loads or stors on same locn"
                   $ locnsUnique $ rtrace role
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

      chansUsed =
          iter c []               
          where
            c = rtrace role
            iter [] soFar = soFar
            iter (e : rest) soFar =
                case evtChan e of
                  Just ch -> iter rest $ adjoin ch soFar
                  Nothing -> iter rest soFar

      checkChanDecl str ch =
          failwith
          ((show ch) ++ " declared " ++ str ++
           " but not used in role " ++
           (rname role))
          $ ch `elem` chansUsed 

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

{--
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
--}


locnsUnique :: Trace -> Bool
locnsUnique [] = True
locnsUnique ((In (ChMsg ch _)) : c') =
    if isLocn ch
    then
        checkLoads c' [ch]
    else
        locnsUnique c'
    where
      checkLoads ((In (ChMsg ch _)) : c') seen =
          if isLocn ch
          then 
              not (ch `elem` seen) &&
              checkLoads c' (ch : seen)
          else
              locnsUnique c'
      checkLoads c' _ = locnsUnique c'
                        
locnsUnique ((Out (ChMsg ch _)) : c') =
    if isLocn ch
    then
        checkStores c' [ch]
    else locnsUnique c'
    where
      checkStores ((Out (ChMsg ch _)) : c') seen =
          if isLocn ch
          then 
              not (ch `elem` seen) &&
              checkStores c' (ch : seen)
          else
              locnsUnique c'
      checkStores c' _ = locnsUnique c'

locnsUnique (_ : c') = locnsUnique c'
    

{-- 
    check c []
    where
      check [] _ = True
      check ((In (ChMsg ch _)) : c') loads
          | isLocn ch              = not(ch `elem` loads) &&
                                     check c' (ch : loads)
          | otherwise              = check c' []
      check ((Out (ChMsg ch _)) : c') loads
          | isLocn ch              =
              (case deleteWhenPresent ch loads of
              Nothing -> False
              Just rest -> check c' rest)
          | otherwise              = check c' []
      check (_ : c') _             = check c' []
      --}


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

loadCritSecs :: MonadFail m => [SExpr Pos] -> m [(Int, Int)]
loadCritSecs [] = return []
loadCritSecs (L pos [(N _ i), (N _ j)] : rest)
    | j<i = fail (shows pos "loadCritSecs:  Bad int pair out of order")
    | otherwise =
        do
          pairs <- loadCritSecs rest
          return ((i,j) : pairs)
loadCritSecs s = fail ("loadCritSecs:  Malformed int pairs: " ++ (show s))

stateSegments :: Trace -> [(Int,Int)]
stateSegments c =
    findSegments [] 0 c
    where
      -- findSegments soFar index c
      -- is called when the original trace has the state segments
      -- soFar that are completed *before* index, and the tail c of
      -- the original trace remains to be explored.
      
      findSegments soFar _ [] = soFar
                                
      findSegments soFar i (In (ChMsg ch _) : c)
          | isLocn ch           = findLower soFar i (i+1) c          
          | otherwise           = findSegments soFar (i+1) c

      findSegments soFar i ((Out (ChMsg ch _)) : c)
          | isLocn ch           = findUpper soFar i (i+1) c           
          | otherwise           = findSegments soFar (i+1) c

      findSegments soFar i (_ : c) =
          findSegments soFar (i+1) c

      findLower soFar i j [] = (i,j-1) : soFar
                               
      findLower soFar i j (In (ChMsg ch _) : c')
          | isLocn ch           = findLower soFar i (j+1) c'
          | otherwise           = findSegments ((i,j-1) : soFar) (j+1) c'
                                  
      findLower soFar i j (In _ : c') = findSegments ((i,j-1) : soFar) (j+1) c'

      findLower soFar i j (Out m : c') = findUpper soFar i j (Out m : c')

      findUpper soFar i j [] = (i,j-1) : soFar

      findUpper soFar i j (Out (ChMsg ch _) : c')
          | isLocn ch           = findUpper soFar i (j+1) c'
          | otherwise           = findSegments ((i,j-1) : soFar) (j+1) c'
                                  
      findUpper soFar i j (Out _ : c') = findSegments ((i,j-1) : soFar) (j+1) c'

      findUpper soFar i j (In m : c') = findSegments ((i,j-1) : soFar) j (In m : c')

{--      -- findEnd soFar i j bool c

      -- is called where the original trace has the state segments
      -- soFar that are completed *before* i, and there is a state
      -- segment that began at i and may still extend; we are
      -- currently inspecting index j which is the start of the
      -- unexplored suffix c; the boolean flag is True if we're in the
      -- upper storing part of the state segment, and False in the
      -- lower loading part.

      findEnd soFar i j _ [] = (i,j-1) : soFar
                                     
      findEnd soFar i j False ((In (ChMsg ch _)) : c')
          | isLocn ch           = findEnd soFar i (j+1) False c'
          | otherwise           = findSegments ((i,j-1) : soFar) (j+1) c'
      findEnd soFar i j False ((Out (ChMsg ch _)) : c')
          | isLocn ch           = findEnd soFar i (j+1) True c'
          | otherwise           = findSegments ((i,j-1) : soFar) (j+1) c'
                                  
      findEnd soFar i j True (In m : c') =
          findSegments ((i,j-1) : soFar) j (In m : c')
      findEnd soFar i j True (Out (ChMsg ch _) : c') 
          | isLocn ch           = findEnd soFar i (j+1) True c'
          | otherwise           = findSegments ((i,j-1) : soFar) (j+1) c'
              
      findEnd soFar i j _ (_ : c') =
          findSegments ((i,j-1) : soFar) (j+1) c'
--}
                       
      

{-    findSegments [] 0 c
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
                       
      -- in the previous case we save the start of c for findSegments
      -- to decide what to do.

      findEnd soFar start i ((In (ChMsg ch _)) : c) False
          | isLocn ch           = findEnd soFar start(i+1) c False
          | otherwise           = findSegments ((start,(i-1)) : soFar) (i+1) c
      findEnd soFar start i ((Out (ChMsg ch _)) : c) _
          | isLocn ch           = findEnd soFar start (i+1) c True
          | otherwise           = findSegments ((start,(i-1)) : soFar) (i+1) c

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

-- Are there any locations used in the role?
hasLocn :: Role -> Bool
hasLocn rl =
  any isLocn (tchans (rtrace rl))

initPreRuleCS :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRuleCS sig gen _ rl pr =
    return (csRules sig gen rl (preruleCs pr))

initPreRulesTrans :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesTrans sig gen _ rl pr =
    return (transRls sig gen rl (preruleTrans pr))

initPreRulesFacts :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesFacts sig gen _ rl pr =
    do
      facts <- loadFactList sig (rvars rl) (preruleFacts pr)
      return (genFactRls sig gen rl facts)

initPreRulesGensts :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesGensts sig gen _ rl pr =
    do
      ts <- loadTerms sig (rvars rl) (preruleGensts pr)
      return (genStateRls sig gen rl ts)

initPreRulesAssumes :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesAssumes sig gen prot rl pr =
    do
      (g,rules,_) <-
          F.foldrM
               (\sexpr (g,rules,n) ->
                    do
                      (g',varConjs) <- loadConclusion sig (annotation sexpr) prot g (rvars rl) sexpr
                      let (g'',newRule) = genOneAssumeRl sig g' rl n varConjs
                      return (g'', newRule : rules, (n+1)))
               (gen,[],0)
               (preruleAssumes pr)
      return (g,rules)

initPreRulesRelies :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesRelies sig gen prot rl pr =
    initRelyGuars sig gen prot rl "rely" (preruleRelies pr)

initPreRulesGuars :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesGuars sig gen prot rl pr =
    initRelyGuars sig gen prot rl "guar" (preruleGuars pr)

initRelyGuars ::  MonadFail m => Sig -> Gen -> Prot -> Role -> String -> [(Int, SExpr Pos)] -> m (Gen, [Rule])
initRelyGuars sig gen prot rl kind =
    F.foldrM
    (\(ht,sexpr) (g,rules) ->
         do
           (g',varConjs) <- loadConclusion sig (annotation sexpr) prot g (rvars rl) sexpr
           () <- varsUsedBy rl (freeVarsInConjLists varConjs) ht (annotation sexpr)
           let (g'',newRule) = genOneRelyGuarRl sig g' rl ht kind varConjs
           return (g'', newRule : rules))
    (gen,[])

initPreRulesCheqs :: MonadFail m => Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])
initPreRulesCheqs sig gen _ rl pr =
    F.foldrM
    (\(ht, pos, v, t) (g,rules) ->
         do
           () <- varsUsedBy rl (varsInTerms [t])  ht pos
           let (g',newRule) = genOneRelyGuarRl sig g rl ht "cheq"
                              [([],[(pos, Equals v t)])] -- stipulate v=t
           return (g', newRule : rules))
    (gen,[])
    (preruleCheqs pr)

varsUsedBy :: MonadFail m => Role -> [Term] -> Int -> Pos -> m ()
varsUsedBy rl vars bound pos =
    case varsUsedHeight rl vars of
      Missing v -> fail ((show pos) ++ " var " ++ (show (varName v))
                         ++ " not bound by height " ++ (show bound))
      FoundAt ht -> if ht <= bound then return ()
                    else fail ((show pos) ++ " variables not bound until height "
                                              ++ (show ht))

iterPreRules :: MonadFail m => (Sig -> Gen -> Prot -> Role -> PreRules -> m (Gen, [Rule])) ->
                Sig -> Gen -> Prot -> [(Role,PreRules)] -> m (Gen, [Rule])
iterPreRules f sig gen prot rlPreRules =
    F.foldrM
         (\(rl,prs) (g,rules) ->
              do
                (g',newRules) <- f sig g prot rl prs
                return (g', newRules ++ rules))
         (gen,[])
         rlPreRules

initRules :: MonadFail m => Sig -> Gen -> Prot -> [(Role,PreRules)] -> m (Gen, [Rule], [Rule])
initRules sig g prot prs =
    -- Must generate neqRules, factRules, assumeRules, relyRules,
    -- guarRules, cheqRules, and,
    -- if b is true, the state rules:
    -- transRules, genStateRules, csRules, and the omnipresent state
    -- rules for
    -- scissors, cake, (inv) shears, and interruptions

    -- let (g',neqs) = neqRules sig g in
    -- let (g'', trans) = transRules g' in
    let anyState = any (\(rl,_) -> hasLocn rl) prs in
    do
      let (g',neqs) = neqRules sig g
      let (g,fixedStateRls) =
              if anyState
              then foldr (\f (g,rules) -> let (g',r) = f g in
                                          (g',r : rules))
                       (g',[])
                       [scissorsRule sig, cakeRule sig, uninterruptibleRule sig,
                        shearsRule sig, invShearsRule sig
                       -- , causeRule sig, effectRule sig
                       ]
              else (g',[])

      (g,fcRls) <- iterPreRules initPreRulesFacts sig g prot prs
      (g,asRls) <- iterPreRules initPreRulesAssumes sig g prot prs
      (g,rlRls) <- iterPreRules initPreRulesRelies sig g prot prs
      (g,grRls) <- iterPreRules initPreRulesGuars sig g prot prs
      (g,cqRls) <- iterPreRules initPreRulesCheqs sig g prot prs

      -- Now here are the ones for states

      (g,trRls) <- iterPreRules initPreRulesTrans sig g prot prs
      (g,csRls) <- iterPreRules initPreRuleCS sig g prot prs
      (g,gsRls) <- iterPreRules initPreRulesGensts sig g prot prs

      return (g,
               neqs ++ fixedStateRls ++ fcRls ++
                    asRls ++ trRls ++ csRls ++ gsRls,
               rlRls ++ grRls ++ cqRls)

{--
  showRoleGenStates :: [(Role,PreRules)] -> [(String,String)]
showRoleGenStates [] = []
showRoleGenStates ((role, pr) : rest) =
    (rname role, concatMap show $ map snd $ preruleGuars pr)
    : showRoleGenStates rest
--}

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

-- Given a list of events, and a list of vars, check that the vars in
-- the Group sorts (rndxs and expts) have the following properties:
--
-- 1.  If the earliest occurrence of a rndx is an In event, that's a
-- state node, ie a load.

-- IMPORTANT:  For now we will not enforce this.  It seems disruptive
-- to examples that use this for certified long-term values,
-- tst/dhcr_um{3,x}.scm, for example.

-- 2.  If the earliest occurrence of a group var is in an In event,
-- then the group var does not *originate* in a later event.  Ie its
-- earliest *carried* occurrence will not be a later transmission.

-- 3.  If the earliest occurrence of a group var is an Out event, that
-- must be an rndx.

badGroupMemberOccurrences :: [Term] -> Trace -> Maybe ([Term], Int)
badGroupMemberOccurrences vars events =
    loop groupVars events 0
    where
      groupVars = filter isVarExpr vars
      usedAndRemaining e = L.partition (flip occursIn $ evtTerm e)

      checkGroupVar (Out _) v = isRndx v
      -- See IMPORTANT note above
      checkGroupVar (In (Plain _)) v = not (isRndx v) || True
      checkGroupVar (In (ChMsg c _)) v = not (isRndx v) || isLocn c || True

      loop _ [] _ = Nothing
      loop gvs (e : evts) i =
          let (fsts,rest) = usedAndRemaining e gvs in
          case L.filter (not . checkGroupVar e) fsts of
            [] -> loop rest evts (i+1)
            bad -> Just (bad,i)

badOrigNotGen :: [Term] -> Trace -> [(Term,Int)]
badOrigNotGen vars events =
    foldr
    (\v soFar -> case recvButOrig v events of
                   Nothing -> soFar
                   Just p -> (v,p) : soFar) [] groupVars
    where
      groupVars = filter isVarExpr vars
      recvButOrig v c =
          if (originates v c &&   -- first carried outbound
              not(generates v c)) -- first occurs inbound
          then
              firstOccursPos v c
          else
              Nothing

loadTrace :: MonadFail m => Sig -> Gen -> [Term] ->
             [SExpr Pos] -> m (Gen, [Term], [Term], PreRules, Trace)
loadTrace sig gen vars xs =
    loadTraceLoop gen [] [] emptyPreRules [] xs
    where
      loadTraceLoop :: MonadFail m => Gen -> [Term] -> [Term] -> PreRules
                    -> Trace -> [SExpr Pos]
                    -> m (Gen, [Term], [Term], PreRules, Trace)
      loadTraceLoop gen newVars uniqs pr events [] =
          let events' = reverse events in
          case badGroupMemberOccurrences vars events' of
            Nothing ->
                case badOrigNotGen vars events' of
                  [] -> return (gen, (vars ++ (reverse newVars)),
                                       (reverse uniqs), pr, events')
                  (v,p) : _ ->
                      fail (shows xs $ " Var received non-carried, the sent carried:  " ++
                                      (show v) ++ " at event " ++ (show p))
            Just (_,i) ->
                fail (shows xs $ " Expts must first be received, rndxs first sent:  " ++
                                " at event " ++ (show i))
      loadTraceLoop gen newVars uniqs pr events ((L _ [S _ "recv", t]) : rest) =
          do
            t <- loadTerm sig vars -- True
                 False t
            loadTraceLoop gen newVars uniqs pr ((In $ Plain t) : events) rest
      loadTraceLoop gen newVars uniqs pr events ((L _ [S _ "send", t]) : rest) =
          do
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs pr ((Out $ Plain t) : events) rest
      loadTraceLoop gen newVars uniqs pr events ((L _ [S _ "recv", ch, t]) : rest) =
          do
            ch <- loadChan sig vars ch
            t <- loadTerm sig vars -- True
                 False t
            loadTraceLoop gen newVars uniqs pr ((In $ ChMsg ch t) : events) rest
      loadTraceLoop gen newVars uniqs pr events ((L _ [S _ "send", ch, t]) : rest) =
          do
            ch <- loadChan sig vars ch
            t <- loadTerm sig vars True t
            loadTraceLoop gen newVars uniqs pr ((Out $ ChMsg ch t) : events) rest
      loadTraceLoop gen newVars uniqs pr events ((L _ [S pos "load", ch, t]) : rest) =
          do
            ch <- loadLocn sig vars ch
            t <- loadTerm sig vars -- True
                 False t
            (gen, pt, pt_t) <- loadLocnTerm sig gen (S pos "pt") (S pos "pval") t
            loadTraceLoop gen (pt : newVars) uniqs pr
                              ((In $ ChMsg ch pt_t) : events) rest

      loadTraceLoop gen newVars uniqs pr events ((L _ [S pos "stor", ch, t]) : rest) =
          do
            ch <- loadLocn sig vars ch
            t <- loadTerm sig vars True t
            (gen, pt, pt_t) <- loadLocnTerm sig gen (S pos "pt") (S pos "pval") t
            loadTraceLoop gen (pt : newVars) (pt : uniqs) pr
                              ((Out $ ChMsg ch pt_t) : events) rest

      loadTraceLoop gen newVars uniqs pr events ((L _ [S pos "rely", form]) : rest) =
          case events of
            [] -> fail (shows pos $ "Rely precedes first event:  " ++ (show form))
            (In _) : _ ->
                loadTraceLoop gen newVars uniqs
                              (preRulesAddRely pr ((L.length events), form))
                              events rest
            _ -> fail (shows pos $ "Rely must follow recv or load:  " ++ (show form))

      loadTraceLoop gen newVars uniqs pr events ((L _ [S pos "guar", form]) : rest) =
          case rest of
            [] -> fail (shows pos $ "Guarantee follows last event:  " ++ (show form))
            (L _ (S _ "stor" : _) : _) ->
                loadTraceLoop gen newVars uniqs
                                  (preRulesAddGuar pr (1+(L.length events), form))
                                  events rest
            (L _ (S _ "send" : _) : _) ->
                loadTraceLoop gen newVars uniqs
                                  (preRulesAddGuar pr (1+(L.length events), form))
                                  events rest
            _ -> fail (shows pos $ "Guarantee must precede send or stor:  " ++ (show form))

      loadTraceLoop gen newVars uniqs pr events ((L _ [S pos "cheq", src, tgt]) : rest) =
          case rest of
            [] -> fail (shows pos $ "cheq must precede some event:  " ++ (show src) ++ ", " ++ (show tgt))
            _ ->
                do
                  src <- loadTerm sig vars False src
                  tgt <- loadTerm sig vars False tgt
                  loadTraceLoop gen newVars uniqs
                                (preRulesAddCheq pr
                                 (1+(L.length events), pos, src, tgt))
                                events rest

      loadTraceLoop _ _ _ _ _ ((L pos [S _ dir, _, _]) : _) =
          fail (shows pos $ "Unrecognized direction " ++ dir)

      loadTraceLoop _ _ _ _ _ (x : _) =
          fail (shows (annotation x) "Malformed event")

loadChan :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadChan sig vars x =
  do
    ch <- loadTerm sig vars False x
    case isChan ch of
      True -> return ch
      False -> fail (shows (annotation x) "Expecting a channel")

loadLocn :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadLocn sig vars x =
  do
    ch <- loadTerm sig vars False x
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

findPreskel :: MonadFail m => Pos -> [Prot] ->
               [SExpr Pos] -> m Preskel
findPreskel pos ps (S _ name : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> loadPreskel (psig p) pos p xs
findPreskel pos _ _ = fail (shows pos "Malformed skeleton")

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
loadInsts sig top p kvars gen insts (L pos (S _ "defstrandmax" : x) : xs) =
    case x of
      S _ role : env ->
          do
            (gen, i) <- loadInstMax sig pos p kvars gen role env
            loadInsts sig top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrandmax")
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
        order nr ar ur ug ab pr cn au fs pl leads genSts kcomment
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
      leads = assoc "leads-to" xs
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

loadInstMax :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> Gen -> String ->
               [SExpr Pos] -> m (Gen, Instance)
loadInstMax sig pos p kvars gen role env =
    do
      r <- lookupRole pos p role
      let height = length (rtrace r)
      let vars = rvars r
      (gen', env') <- foldM (loadMaplet sig kvars vars)
                      (gen, emptyEnv) env
      return (mkInstance gen' r env' height)

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
            [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr Pos] -> [SExpr ()] -> m Preskel
loadRest sig pos vars p gen gs insts orderings
         nr ar ur ug ab pr cn au fs pl leads genSts comment =
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
      lds <- loadOrderings heights leads
      genSts <- loadTerms sig vars genSts
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
        Return () -> return
                     $ applyLeadsTo k lds
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
    t <- loadTerm sig vars False x
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
findGoal :: MonadFail m => Pos -> [Prot] -> [SExpr Pos] -> m Preskel
findGoal pos ps (S _ name : x : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p ->
        do
          let sig = psig p
          (g, goal, antec) <- loadSentence sig RoleSpec pos p (pgen p) x
          let (gs, xs') = findAlist xs
          (g, goals) <- loadGoals sig pos p g gs
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

loadGoals :: MonadFail m => Sig -> Pos -> Prot -> Gen ->
             [SExpr Pos] -> m (Gen, [Goal])
loadGoals _ _ _ g [] = return (g, [])
loadGoals sig pos prot g (x : xs) =
  do
    (g, goal, _) <- loadSentence sig RoleSpec pos prot g x
    (g, goals) <- loadGoals sig pos prot g xs
    return (g, goal : goals)
