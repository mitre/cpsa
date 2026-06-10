-- Computes the cohort associated with a skeleton or its generalization

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Cohort (Mode(..), ReduceRes(..), reduce, unrealized) where

import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.List as L
import Control.Parallel
import CPSA.Algebra
import CPSA.Channel
import CPSA.Protocol
import CPSA.Operation
import CPSA.Strand

{-- Debugging support
import System.IO.Unsafe
import Control.DeepSeq

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zShow :: Show a => a -> a
zShow x = z (show x) x

kShow :: Preskel -> Preskel 
kShow k = 
    if L.length (strands k) == 5 then 
      zShow k
    else 
      k 
goodParent :: Preskel -> Bool
goodParent k = 
  let xs = insts k in 
  (L.length xs == 5) &&
    ("short-init" == (rname $ role (xs !! 2))) &&
    ("short-short-init" == (rname $ role (xs !! 3))) &&
    ("resp" == (rname $ role (xs !! 4)))

goodChild :: Preskel -> Bool 
goodChild k = 
  let xs = insts k in 
  L.length xs == 4 &&
    "short-short-init" == (rname $ role (xs !! 2)) &&
    "resp" == (rname $ role (xs !! 3))

tShow1 :: Show a => Preskel -> Preskel -> a -> Preskel 
tShow1 k k' _ = 
  if goodParent k && goodChild k' then 
    z (show ("parent", k)) k
  else 
    k

--   tShow2 :: Show a => Preskel -> Preskel -> a -> Preskel 
--   tShow2 k k' _ = 
--     if goodParent k && goodChild k' then
--       --z (show ("child", k')) k'
--       z (show "perm: " ++ show (compressUpdate 4 2 [0,1,3,4])) k'
--     else 
--       k'

tShow3 :: Show a => Preskel -> Preskel -> a -> a
tShow3 k k' m = 
  if goodParent k && goodChild k' then 
    z (show ("mapping", m)) m
  else 
    m

zz :: Show a => a -> a
zz x = z x x

zn :: Show a => a -> Maybe b -> Maybe b
zn x Nothing = z x Nothing
zn _ y = y

zf :: Show a => a -> Bool -> Bool
zf x False = z x False
zf _ y = y

zt :: Term -> String
zt t =
    show (displayTerm (addToContext emptyContext [t]) t)

zs :: Set Term -> String
zs s =
    show $ map (displayTerm (addToContext emptyContext ts)) ts
    where
      ts = S.toList s

zl :: Show a => [a] -> [a]
zl a = z (length a) a

zi :: Instance -> String
zi inst =
    show (map f e)
    where
      domain = rvars (role inst)
      e = reify domain (env inst)
      range = map snd e
      f (x, t) = (displayTerm (context domain) x,
                  displayTerm (context range) t)
      context ts = addToContext emptyContext ts
--}

-- Compile time switches for expermentation.

-- Include the escape set in the set of target terms
useEscapeSetInTargetTerms :: Bool
useEscapeSetInTargetTerms = False -- True

-- Filter a cohort for skeletons that solve the test.  Turn off only
-- to debug the other parts of the test solving algorithm.
useSolvedFilter :: Bool
useSolvedFilter = True -- False

-- Use thinning during generalization.
useThinningDuringGeneralization :: Bool
useThinningDuringGeneralization = False -- True

omitGeneralization :: Bool
omitGeneralization = False -- True

-- EXPERIMENT (global shapes): deorigination (wonthull2 completeness fix) and
-- global-shape generalization are now RUNTIME flags carried in Mode
-- (deorig, globalShapes), set from Options.  See transformingNode and
-- Strand.generalize.

-- This check is just a sanity check and is normally left off.
usePovCheck :: Bool
usePovCheck = True -- False

-- Minimum priority to solve
minPriority :: Int
minPriority = 1

-- Penetrator derivable predicate and checking for unrealized skeletons.

derivable :: Set Term -> Set Term -> Term -> Bool
derivable avoid sent term =
    let (knowns, unknowns) = decompose sent avoid in
    buildable knowns unknowns term

-- Returns the nodes in a preskeleton that are not realized.
unrealized :: Preskel -> [Node]
unrealized k =
    foldl unrealizedInStrand [] (strands k)
    where
      (a, _) = avoid k
      unrealizedInStrand acc s =
          fst $ foldl unrealizedInNode (acc, S.empty) (nodes s)
      unrealizedInNode (acc, ns) n =
          case inbnd $ event n of
            Nothing -> (acc, ns)
            Just t ->
              case () of
                _ | S.member t (cmsInNodes ns') ->
                      -- If channel message is sent, the node is realized
                      (acc, ns')
                  | authCm k t ->
                      -- If channel message is authenticated
                      -- the channel message is a critical value
                      (graphNode n : acc, ns')
                  | derivable a ts (cmTerm t) ->
                      -- If derivable, node is realized
                      (acc, ns')
                  | otherwise ->
                      -- A term is a critical value
                      (graphNode n : acc, ns')
              where
                ns' = addSendingBefore ns n
                ts = termsInNodes k ns'

addSendingBefore :: Set Vertex -> Vertex -> Set Vertex
addSendingBefore s n =
    foldl addSending s (preds n)
    where
      addSending s n
        | S.member n s = s
        | otherwise = addSendingBefore (addIfSending s n) n
      addIfSending s n =
          case outbnd $ event n of
            Nothing -> s
            Just _ -> S.insert n s

cmsInNodes :: Set Vertex -> Set ChMsg
cmsInNodes ns =
  S.map (evtCm . event) ns

-- Find public messages excluding terms sent on confidential channels
termsInNodes :: Preskel -> Set Vertex -> Set Term
termsInNodes k ns =
  S.map cmTerm (S.filter (not . confCm k) $ cmsInNodes ns)

-- Find confidential channel messages
confsInNodes :: Preskel -> Set Vertex -> Set ChMsg
confsInNodes k ns =
  S.filter (confCm k) $ cmsInNodes ns

-- Returns that atoms that cannot be guess when determining if a
-- term is derivable from some other terms, and the atoms that
-- uniquely originate or generate in this skeleton.
avoid :: Preskel -> (Set Term, [Term])
avoid k =
    (S.fromList (knon k ++ p ++ u ++ g),
      L.nub (p ++ u ++ g))
    where
      p = kpnon k
      u = uniqOrig k
      g = uniqGen k

-- Suppose k --v,p-> k', where k |-phi,sigma-> k'.  Let t=msg(k, v)@p,
-- t'=sigma(t), T=sigma(esc(k, v, t)), and t''=msg(k', phi(v)).
-- Position p is solved in k' from k at v if:
--
-- 1. some member of anc(t'', p) is in T', or
--
-- 2. for some t in outpred(k', phi(v)), t' is not carried only within
--    T in t, or
--
-- 3. targetterms(t', T) \ sigma(targetterms(t, esc(k, v, t))) /= empty
--    and there are variables in k's protocol that are not atoms, or
--
-- 4. the decryption key for an element of T is derivable, or
--
-- 5. t' is an encryption and the encryption key for t' is derivable.
--
-- 6. t' is derivable in k' at phi(v).
--
-- 7. k' has a distinct absent constraint
--
-- Haskell variables:
-- ct     = t
-- pos    = p
-- ek     = encription key if ct is an encyption else nothing
-- escape = esc(k, v, t)
-- k      = k'
-- n      = v
-- subst  = sigma
solved :: CMT -> Place -> [Term] -> Set CMT ->
          Preskel -> Node -> Subst -> [(Term, Term)] -> Bool
solved ct pos eks escape k n subst absent =
    -- Condition 1
    isAncestorInSet escape' t pos ||
    -- Condition 1a, needed for DH according to Moses
    derivable a (excludeConf k escape') (cmtTerm ct') ||
    -- Condition 2
    any (not . carriedOnlyWithin ct' escape') (S.toList $ cmsInNodes vs) ||
    -- Condition 3
    not (varsAllAtoms (protocol k)) && not (S.null targetTermsDiff) ||
    -- Condition 4
    any (maybe False (derivable a ts) . decryptionKey) (S.toList encs) ||
    -- Condition 5
    -- Bug fix: apply subst to eks
    any (derivable a ts) (map (substitute subst) eks) ||
    -- Condition 6
    derivable a ts (cmtTerm ct') ||
    -- Condition 7: hack?
    length (kabsent k) > length absent
    where
      v = vertex k n            -- Look up vertex in k
      t = evtCm (event v)       -- Term at v
      ct' = cmtSubstitute subst ct -- Mapped critical term
      escape' = S.map (cmtSubstitute subst) escape
      mappedTargetTerms = S.map (cmtSubstitute subst) (targetTerms ct escape)
      targetTermsDiff = S.difference (targetTerms ct' escape') mappedTargetTerms
      vs = addSendingBefore S.empty v
      ts = termsInNodes k vs     -- Outbound non-conf predecessors
      (a, _) = avoid k
      encs = S.foldr f S.empty escape'
      f (CM _) ts = ts
      f (TM t) ts = S.insert t ts

-- A sanity check for cohort members normally left off.
povCheck :: Preskel -> Bool
povCheck k =
    case pov k of
      Nothing -> True
      Just k0 -> not (null (homomorphism k0 k (prob k)))

maybeSolved :: CMT -> Place -> [Term] -> Set CMT ->
               Preskel -> Node -> Subst -> [(Term, Term)] -> Bool
maybeSolved ct pos eks escape k n subst absent =
    not useSolvedFilter
            || solved ct pos eks escape k n subst absent
               && (not usePovCheck || povCheck k)
                          -- ||
                          --  (z ("povCheck failed " ++
                          --      (show (case pov k of
                          --               Nothing -> Nothing
                          --               Just k0 -> Just (prob k0))))
                          --   False))

data Mode = Mode
    { noGeneralization :: Bool,
      nonceFirstOrder :: Bool,
      visitOldStrandsFirst :: Bool,
      reverseNodeOrder :: Bool,
      -- EXPERIMENT (global shapes): runtime flags, formerly the compile-time
      -- constants useGlobalShapes (Strand.hs) and useDeorigination (here).
      globalShapes :: Bool,     -- generalization = listener deletion only
      deorig :: Bool }          -- deorigination augmentation fix on
    deriving Show

excludeConf :: Preskel -> Set CMT -> Set Term
excludeConf k cm =
  S.map cmtTerm (S.filter f cm)
  where
    f (CM cm) = not $ confCm k cm
    f (TM _) = True

parFoldr :: (a -> b -> b) -> b -> [a] -> b
parFoldr _ b [] = b
parFoldr f b (a : as) =
    par b' (f a b')
    where
      b' = parFoldr f b as

-- Desired functionality, given a skeleton k.

-- If some node in k is unrealized, then find a test for it; compute
-- the cohort; close each cohort member under the rules using
-- simplify.  Return the list of results simpKs factored by
-- isomorphism, labeled as Crt simpKs.
--
-- If this is Crt [], then k is dead.

-- If no node in k is unrealized, then close under the rules,
-- obtaining 0 or more results factored by isomorphism.

-- If just one k' is present in these results, and k' is isomorphic to
-- k, then k is realized.  Check whether k can be generalized,
-- returning Gnl ks, where ks are the results (factored by
-- isomorphism) of simplifying the generalized versions.  When k
-- cannot be generalized, Return Stable, since it is a successful
-- terminal value for the branch.

-- If multiple nonisomorphic results ks are obtained from simplifying
-- k, return Crt ks.

-- Previous comment, which was less explicit:

--   -- Abort if there is an unrealized node without a test, otherwise
--   -- return a list of skeletons that solve one test.  If the skeleton is
--   -- realized, try to generalize it, but only when noIsoChk is false.
--   -- After all of that, apply rewrite rule and filter output that makes
--   -- no progress.

data ReduceRes = Stable | Crt [Preskel] | Gnl [Preskel] -- now needed

-- simplify 

--   simplifyNonIsomorphic :: Preskel -> [Preskel]
--   simplifyNonIsomorphic = factorIsomorphicPreskels . simplify

reduceNoTest :: Mode -> Preskel -> ReduceRes
reduceNoTest mode k =
  if omitGeneralization || noGeneralization mode then Stable
  else
      -- EXPERIMENT (global shapes): globalShapes flag threaded to maximize.
      (case maximize (globalShapes mode) k of --filterSame k (maximize k) of
          [] -> Stable
          ks -> Gnl ks)
    {- case [k] --   simplify (k { operation = AppliedRules (strandids k),
         --                          krules = [] })
    of
      [k']
          | isomorphic (gist k) (gist k') ->
              if omitGeneralization || noGeneralization mode then Stable
              else
                  (case maximize k of
                     [] -> Stable
                     ks -> Gnl ks)
          | True -> Crt [k'] -}
      {- ks -> Crt (mgsCall $ filterSame k ks)
    where
      mgsCall ks = mgs $ map (\k -> (k,(getStrandMap $ operation k))) ks -}

reduce :: Mode -> Preskel -> ReduceRes
reduce mode k =
    case findTest mode k u a of
      Nothing -> reduceNoTest mode k
      Just ks ->                -- normal cohort for selected unrealized node
        Crt (filterSame
             k (factorIsomorphicPreskels (parFoldr -- remove isomorphic duplcates *after* simplify
                (\k soFar -> (simplify k) ++ soFar)
                [] ks)))
    where
      (a, u) = avoid k

-- Filter out skeletons in ks that are isomorphic to k.
filterSame :: Preskel -> [Preskel] -> [Preskel]
filterSame k ks =
  filter f ks
  where
    f k' = not $ probIsomorphic k k' -- isomorphic (gist k) (gist k')

prioritizeVertices :: Preskel -> [Vertex] -> [Vertex]
prioritizeVertices k vs =
     map fst $ filter keep $ L.sortBy prios $ map addPrio vs
     where
       addPrio v = (v, priority k (sid $ strand v, pos v))
       prios (_, p) (_, p') = compare p' p
       keep (_, p) = p >= minPriority

priority :: Preskel -> Node -> Int
priority k (s, i) =
  case lookup (s, i) (kpriority k) of
    Just p -> p
    Nothing -> rpriority (role $ insts k !! s) !! i

nodeOrder :: Mode -> Preskel -> [Vertex]
nodeOrder mode k =
    concatMap (nodeVisitOrder mode) (strandVisitOrder mode (strands  k))

strandVisitOrder :: Mode -> [a] -> [a]
strandVisitOrder mode ss =
    if visitOldStrandsFirst mode then
        ss                      -- Visit old strands first
    else
        reverse ss     -- Visit recently added strands first (default)

nodeVisitOrder :: Mode -> Strand -> [Vertex]
nodeVisitOrder mode s =
    if reverseNodeOrder mode == rsearch (role $ inst s) then
        nodes s                -- Visit earliest nodes first (default)
    else
        reverse $ nodes s       -- Visit latest nodes first

-- Look for a test node in a strand
findTest :: Mode -> Preskel -> [Term] -> Set Term -> Maybe [Preskel]
findTest mode k u a =
    loop (prioritizeVertices k $ nodeOrder mode k)
    where
      loop [] = Nothing
      loop (n : nodes) =
          case inbnd $ event n of
            Nothing -> loop nodes
            Just t ->
              case () of
                _ | S.member t (cmsInNodes ns) ->
                      -- If previous node sent channel message, node
                      -- is realized
                      loop nodes
                  | authCm k t ->
                      -- If channel message is authenticated
                      -- the channel message is a critical value
                      Just $ chanSolveNode (deorig mode) k (graphNode n) t
                  | buildable ts' a' (cmTerm t) ->
                      -- If derivable, node is realized
                      loop nodes
                  | otherwise ->
                      -- A term is a critical value
                      Just $ testNode mode k u cms ts' a' (graphNode n) t
              where
                ns = addSendingBefore S.empty n
                ts = termsInNodes k ns    -- Public messages
                (ts', a') = decompose ts a
                cms = confsInNodes k ns

-- Look for a critical term that makes this node a test node.
testNode :: Mode -> Preskel -> [Term] -> Set ChMsg -> Set Term ->
            Set Term -> Node -> ChMsg -> [Preskel]
testNode mode k u cms ts a n cm =
  loop $ potentialCriticalMessages mode u ts a $ cmTerm cm
  where
    loop [] = error (
      "Cohort.testNode missing test at " ++ show n ++ "\n" ++ show cm)
    loop ((ct, eks) : cts) =
      case escapeSet ts a ct of
        Nothing -> loop cts
        Just esc ->
          places (cmtCarriedPlaces (TM ct) cm)
          where
            places [] = loop cts  -- Find position at which
            places (p : ps)       -- ct has escaped
              | isAncestorInSet escape cm p = places ps
              | otherwise = solveNode (deorig mode) k a (TM ct) p eks n cm escape
            escape = S.union    -- The escape set has type CMT
                     (S.map TM esc)
                     (S.map CM (S.filter (carriedBy ct . cmTerm) cms))

potentialCriticalMessages :: Mode -> [Term] -> Set Term ->
                             Set Term -> Term -> [(Term, [Term])]
potentialCriticalMessages mode u ts a t =
  if nonceFirstOrder mode then
    nonces ++ encs
  else
    encs ++ nonces
  where
    nonces = map f (filter (flip carriedBy t) u) ++
             (foldCarriedTerms fnum [] t)
    encs = filter g (map h (encryptions t))
    fnum nums t | isNum t && (not $ buildable ts a t) = nums ++ [(t, [])]
                | otherwise = nums
    f ct = (ct, [])             -- A nonce tests has no eks
    g (_, []) = False           -- An encryption test must have
    g _ = True                  -- at least one non-derivable key
    -- Dump derivable encryption keys
    h (ct, eks) = (ct, filter (not . buildable ts a) eks)

carriedOnlyWithin :: CMT -> Set CMT -> ChMsg -> Bool
carriedOnlyWithin target escape source =
    all (isAncestorInSet escape source) (cmtCarriedPlaces target source)

-- isAncestorInSet set source position is true if there is one ancestor of
-- source at position that is in the set.
isAncestorInSet :: Set CMT -> ChMsg -> Place -> Bool
isAncestorInSet set source position =
    any (flip S.member set) (cmtAncestors source position)

-- Solve critical message at position pos at node n.
-- ct = t @ pos
-- t  = msg(k, n)
-- EXPERIMENT (global shapes): deorig threaded through to augmentations.
solveNode :: Bool -> Preskel -> Set Term -> CMT -> Place -> [Term] -> Node ->
             ChMsg -> Set CMT -> [Preskel]
-- solveNode _ _ _ _ _ _ _ = []
solveNode deorig k a ct pos eks n t escape =
    mgs $ cons ++ augs ++ lsns ++ dhs
    where
      cons = contractions k ct pos eks n t escape cause
      augs = augmentations deorig k ct pos eks n escape cause
      lsns = addListeners k ct pos eks n t escape cause
      dhs = theDHSubcohort k a ct pos eks n escape cause
      cause = Cause (dir eks) n ct escape

-- Authenticated channel message is the critical value
-- EXPERIMENT (global shapes): deorig threaded through to augmentations.
chanSolveNode :: Bool -> Preskel -> Node -> ChMsg -> [Preskel]
chanSolveNode deorig k n ct =
  mgs $ augmentations deorig k t pos eks n escape cause
  where
    t = CM ct
    pos = Place []
    eks = []
    escape = S.empty
    cause = Cause Channel n t escape

-- Filter out all but the skeletons with the most general homomorphisms.

mgs :: [(Preskel, [Sid])] -> [Preskel]
mgs cohort =
  --reverse $ map recordMap $ loop (dropNonInjective cohort) []
  reverse $ map recordMap $ loop cohort []
  where
    loop [] acc = acc
    loop (kphi : cohort) acc
      | any (f kphi) cohort || any (f kphi) acc =
        loop cohort acc
      | otherwise = loop cohort (kphi : acc)
    f (k, phi) (k', phi') =
        let ans = any (not. null . homomorphism k' k)
                  (composeFactors (strandids k) (strandids k') phi phi') in
        ans
    recordMap (k, phi) = updateStrandMap phi k

-- dropNonInjective :: [(Preskel, [Sid])] -> [(Preskel, [Sid])]
-- dropNonInjective cohort = 
--   filter (isInjective . snd) cohort
--   where 
--     isInjective phi = L.nub phi == phi

-- Given two permutations p and p', with ranges r and r', this
-- function returns the list of permutations p'' such that
--
--    p'' o p' = p.
--
-- This function no longer assumes p' is injective but it returns permutations
-- that are.

composeFactors :: [Int] -> [Int] -> [Int] -> [Int] -> [[Int]]
composeFactors r r' p p' =
  filter isInjective $ perms (zip p' p) r r'
  where isInjective phi = L.nub phi == phi
  --perms (zip p' p) (filter (flip notElem p) r) r' -- JDR-era code

perms :: [(Int, Int)] -> [Int] -> [Int] -> [[Int]]
perms _ _ [] = [[]]
perms alist range (s:domain) =
  case lookup s alist of
    Just s' -> [ s':ss | ss <- perms alist range domain ]
    Nothing -> [ s':ss | s' <- range, ss <- perms alist range domain ]

-- Contractions

-- Contract the critical message at the given position.
contractions :: Preskel -> CMT -> Place -> [Term] -> Node -> ChMsg ->
                Set CMT -> Cause -> [(Preskel, [Sid])]
contractions k ct pos eks n t escape cause =
    [ (k', phi) |
           let anc = cmtAncestors t pos,
           subst <- solve escape anc (gen k, emptySubst) ++
                    constSolve (gen k, emptySubst) ct,
           (k', n, phi, subst') <- contract k n cause subst,
           maybeSolved ct pos eks escape k' n subst' (kabsent k) ]

constSolve :: (Gen, Subst) -> CMT -> [(Gen, Subst)]
constSolve subst ct =
    [ s | c <- consts (cmtTerm ct),
          s <- unify (cmtTerm ct) c subst]

solve :: Set CMT -> [CMT] -> (Gen, Subst) -> [(Gen, Subst)]
solve escape ancestors subst =
    [ s | e <- S.toList escape,
          a <- ancestors,
          s <- cmtUnify a e subst ]

carriedOnlyWithinAtSubst :: CMT -> Set CMT -> ChMsg -> (Gen, Subst) -> Bool
carriedOnlyWithinAtSubst  ct escape t (_, subst) =
    carriedOnlyWithin ct' escape' t'
    where
      ct' = cmtSubstitute subst ct
      escape' = S.map (cmtSubstitute subst) escape
      t' = cmSubstitute subst t

fold :: CMT -> Set CMT -> ChMsg -> (Gen, Subst) -> [(Gen, Subst)]
fold ct escape t (gen, subst) =
    [ (gen', compose subst' subst) |
      (gen', subst') <- foldl f [(gen, emptySubst)] (cmtCarriedPlaces ct' t') ]
    where
      ct' = cmtSubstitute subst ct
      escape' = S.map (cmtSubstitute subst) escape
      t' = cmSubstitute subst t
      f substs p =
          [ s | subst <- substs, s <- solve escape' (cmtAncestors t' p) subst ]

dir :: [a] -> Direction
dir [] = Nonce
dir _ = Encryption

-- Augmentations

-- EXPERIMENT (global shapes): deorig threaded through to transformingNode.
augmentations :: Bool -> Preskel -> CMT -> Place -> [Term] -> Node ->
                 Set CMT -> Cause -> [(Preskel, [Sid])]
augmentations deorig k ct pos eks n escape cause =
    [ k' | r <- roles (protocol k),
           k' <- roleAugs deorig k ct pos eks n escape cause targets r ]
    where
      targets = S.toList (targetTerms ct escape)

roleAugs :: Bool -> Preskel -> CMT -> Place -> [Term] -> Node -> Set CMT ->
            Cause -> [CMT] -> Role -> [(Preskel, [Sid])]
roleAugs deorig k ct pos eks n escape cause targets role =
    [ (k', phi) |
           (subst', inst) <-
               transformingNode deorig ct escape targets role subst,
           (k', n', phi, subst'') <-
               augment k n cause role subst' inst,
           maybeSolved ct pos eks escape k' n' subst'' (kabsent k)]
    where
      subst = cloneRoleVars (gen k) role

-- Generate a fresh set of role variables
cloneRoleVars :: Gen -> Role -> (Gen, Subst)
cloneRoleVars gen role =
    grow (rvars role) gen emptyEnv
    where
      grow [] gen env = (gen, substitution env)
      grow (t : ts) gen env =
          let (gen', t') = clone gen t in
          case match t t' (gen', env) of
            (gen'', env') : _ -> grow ts gen'' env'
            [] -> error "Cohort.grow: Internal error"

-- EXPERIMENT (global shapes): deorig is the runtime deorigination flag,
-- threaded from solveNode/chanSolveNode (Mode field deorig).
transformingNode :: Bool -> CMT -> Set CMT -> [CMT] -> Role ->
                    (Gen, Subst) -> [((Gen, Subst), Instance)]
transformingNode deorig ct escape targets role subst =
    loop 1 [] [] (rtrace role)
    where
      -- loop height past acc trace
      loop _ _ acc [] = acc
      loop ht past acc (In t : c) =
          loop (ht + 1) (In t : past) acc c
      loop ht past acc (Out t : c) =
          loop (ht + 1) (Out t : past) acc' c
          where
            substs = carriedBindings targets t subst
            substs' = cowt ct escape past substs
            -- DEORIGINATION (wonthull2 fix), gated by the deorig flag:
            -- when on, also offer the receive-instead-of-originate
            -- alternatives; when off, this is exactly stock (substs').
            substs'' = if deorig
                       then concatMap (deoriginate ct escape past) substs'
                       else substs'
            acc' = maybeAug ct escape role ht substs'' acc t

-- True when the critical term is already carried somewhere in some past
-- reception (regardless of the escape set) under the substitution.  When
-- it is, no deorigination is needed.  Deorigination matters only when
-- the critical term is absent from every reception, so the strand would
-- otherwise ORIGINATE it (the wonthull2 send-only-variable case).
receivedAtAll :: CMT -> Trace -> (Gen, Subst) -> Bool
receivedAtAll ct past (_, subst) =
    any rcv [ inT | In inT <- past ]
    where
      ct' = cmtSubstitute subst ct
      rcv inT = not (null (cmtCarriedPlaces ct' (cmSubstitute subst inT)))

-- Keep the originating substitution and, when the critical term is not
-- received anywhere, also offer alternatives that bind a received
-- subterm to the critical term and fold it within the escape set
-- (generating the missing reception).  Unlike the earlier attempt this
-- does NOT replace the originating candidate: both flow on to mgs.
deoriginate :: CMT -> Set CMT -> Trace -> (Gen, Subst) -> [(Gen, Subst)]
deoriginate ct escape past subst
    | receivedAtAll ct past subst = [subst]   -- already received; nothing to add
    | otherwise =
        subst :                               -- KEEP the originating option
        [ s' |
          In inT <- past,
          sub <- S.toList (cmFoldCarriedTerms (flip S.insert) S.empty inT),
          s  <- cmtUnify sub ct subst,        -- receive the critical term
                                              -- (cyclic unifications now fail
                                              -- cleanly in Algebra.unify)
          -- Re-establish carried-only-within over the whole past via the
          -- stock cowt engine (guarded + nubSnd-deduped + fixpoint).
          s' <- cowt ct escape past [s] ]
-- end EXPERIMENT (wonthull2 deorigination) ---------------------------

-- Terms considered for binding with the carried terms in an outbound
-- term.
targetTerms :: CMT -> Set CMT -> Set CMT
targetTerms ct escape =
    if useEscapeSetInTargetTerms then
       targetTermsWithEscapeSet
    else
       S.difference targetTermsWithEscapeSet escape
    where
      targetTermsWithEscapeSet = S.foldr f (S.singleton ct) escape
      f (CM t) ts =
          foldl (flip S.insert) ts
                (concatMap (cmtAncestors t) (cmtCarriedPlaces ct t))
      f (TM t) ts =
        case ct of
          CM _ -> ts
          TM ct ->
            foldl (flip S.insert) ts
                  (map TM $ concatMap (ancestors t) (carriedPlaces ct t))

-- Find bindings for terms in the test.
carriedBindings :: [CMT] -> ChMsg -> (Gen, Subst) -> [(Gen, Subst)]
carriedBindings targets outbound subst =
    [ s |
      subterm <- S.toList (cmFoldCarriedTerms (flip S.insert) S.empty outbound),
      target <- targets,
      s <- cmtUnify subterm target subst ]

-- Ensure the critical term is carried only within the escape set of
-- every term in the past using fold from cows.
cowt :: CMT -> Set CMT -> Trace -> [(Gen, Subst)] -> [(Gen, Subst)]
cowt ct escape c substs =
    nubSnd $ concatMap (cowt0 ct escape c) substs

-- Remove pairs with the same second element.
nubSnd :: Eq b => [(a, b)] -> [(a, b)]
nubSnd substs =
    L.nubBy (\(_, s) (_, s') -> s == s') substs

-- Handle one substitution at a time.
cowt0 :: CMT -> Set CMT -> Trace -> (Gen, Subst) -> [(Gen, Subst)]
cowt0 ct escape c subst =
    if all (f subst) c then     -- Substitution works
        [subst]
    else                        -- Substitution needs refinement
        cowt ct escape c (foldn ct escape c [subst])
    where
      f subst evt =
          carriedOnlyWithinAtSubst ct escape (evtCm evt) subst

-- Apply fold to each message in the trace.
foldn :: CMT -> Set CMT -> Trace -> [(Gen, Subst)] -> [(Gen, Subst)]
foldn _ _ [] substs = substs
foldn ct escape (evt : c) substs =
    foldn ct escape c (concatMap (fold ct escape (evtCm evt)) substs)

-- If the outbound term is carried only within, no transforming node
-- was found, otherwise, add a candidate augmentation to the
-- accumulator.
maybeAug :: CMT -> Set CMT -> Role -> Int -> [(Gen, Subst)] ->
            [((Gen, Subst), Instance)] -> ChMsg ->
            [((Gen, Subst), Instance)]
maybeAug ct escape role ht substs acc t =
    foldl f acc $ L.filter testNotSolved substs
    where
      testNotSolved (_, subst) =
          not $ carriedOnlyWithin
                  (cmtSubstitute subst ct)
                  (S.map (cmtSubstitute subst) escape)
                  (cmSubstitute subst t)
      f acc (gen, subst) =
          case bldInstance role itrace gen of
            (gen, inst) : _ -> ((gen, subst), inst) : acc
            [] -> acc
          where
            itrace = map (evtMap $ substitute subst) (take ht (rtrace role))

-- Listener augmentations

addListeners :: Preskel -> CMT -> Place -> [Term] -> Node -> ChMsg ->
                Set CMT -> Cause -> [(Preskel, [Sid])]
addListeners k ct pos eks n t escape cause =
    [ (k', phi) |
           t' <- filter (f t) (S.toList (escapeKeys eks escape)),
           (k', n', phi, subst) <- addListener k n cause t',
           maybeSolved ct pos eks escape k' n' subst (kabsent k) ]
    where
      f (ChMsg _ _ _) _ = True
      f (Plain t) t' = t /= t'

escapeKeys :: [Term] -> Set CMT -> Set Term
escapeKeys eks escape =
    S.foldr f es escape
    where
      f (TM e) s = maybe s (flip S.insert s) (decryptionKey e)
      f (CM _) s = s
      es = S.fromList eks

-- DH Subcohort

theDHSubcohort :: Preskel -> Set Term ->
                  CMT -> Place -> [Term] -> Node ->
                  Set CMT -> Cause -> [(Preskel, [Sid])]
theDHSubcohort k a ct pos eks n escape cause
  | isBase (cmtTerm ct) = baseDHSubcohort k ct pos eks n escape cause
  | isExpr (cmtTerm ct) = exprDHSubcohort k a ct pos eks n escape cause
  | otherwise = []

baseDHSubcohort :: Preskel -> CMT -> Place -> [Term] ->
                   Node -> Set CMT -> Cause -> [(Preskel, [Sid])]
baseDHSubcohort k ct pos eks n escape cause
  | elem n (kprecur k) = []
  | otherwise =
    [ (k', phi) |
      (k', n', phi, subst) <- addBaseListener k n cause (cmtTerm ct),
      maybeSolved ct pos eks escape k' n' subst (kabsent k)]

exprDHSubcohort :: Preskel -> Set Term ->
                  CMT -> Place -> [Term] -> Node ->
                  Set CMT -> Cause -> [(Preskel, [Sid])]
exprDHSubcohort _ _ ct _ _ _ _ _ | isRndx (cmtTerm ct) = []
exprDHSubcohort k a ct pos eks n escape cause =
  do
    x <- exprVars (cmtTerm ct)
    case S.member x a of
      False -> []
      True ->
        [ (k', phi) |
          (k', n', phi, subst) <- addAbsence k n cause x (cmtTerm ct),
          maybeSolved ct pos eks escape k' n' subst (kabsent k) ] ++
        [ (k', phi) |
          (k', n', phi, subst) <- addListener k n cause x,
          maybeSolved ct pos eks escape k' n' subst (kabsent k) ]

-- Maximize a realized skeleton if possible.  Do not consider
-- generalizations that fail to satisfy the rules of the skeleton's
-- protocol.

{--

The previous version:

maximize :: Preskel -> [Preskel]
maximize k =
    take 1 (filter f gens)      -- Return at most the first answer
    where
      gens = do
        (k', mapping) <- generalize k -- Generalize generates candidates
        specialization k k' mapping   -- Test a candidate
      f k =
        case rewrite k of
          Nothing -> True
          _ -> False

--}

-- EXPERIMENT (global shapes): globalShapes threaded to generalize.
maximize :: Bool -> Preskel -> [Preskel]
maximize globalShapes k =
    iter $ -- factorIsomorphicPreskels $
    concatMap simplify $ map recordMap $ generalize globalShapes k
    where
      iter [] = []
      iter (k' : rest) =
          let mapping = getStrandMap (operation k') in
          -- case z "}" (specialization k (z "{" k') mapping)
          case specialization k k' mapping of
            [] -> iter rest  -- Was:  -- tShow1 k k' mapping `deepseq` tShow2 k k' mapping `deepseq` tShow3 k k' mapping `deepseq` 
            ks -> ks  -- Don't add iter rest. Just take the first successful one.
      recordMap (k, sm) = --if sm == getStrandMap (operation kk)
                          --then kk
                          --else -- z (show $ getStrandMap (operation
                               -- k)) $
                              updateStrandMap sm k -- (, sm) 

-- Test to see if realized skeleton k is a specialization of
-- preskeleton k' using the given strand mapping.  Returns the
-- skeleton associated with k' if it refines k.

specialization :: Preskel -> Preskel -> [Sid] -> [Preskel]
specialization k k' mapping
    | not (preskelWellFormed k') = []     --  (showSome k' [] )
    | otherwise =
        do
          k'' <- toSkeleton useThinningDuringGeneralization k'
          -- (showSome k'' k'') inside *realized* to debug
          case (realized k'') &&  (not (probIsomorphic k k'')) &&
          -- case (realized k'') &&  (not (isomorphic (gist k) (gist k''))) &&
               (refines k'' (pov k'') (prob k'')) &&
               (refines k (Just k'') mapping) of
            True -> [k''] -- maybeOK $
            False -> [] 
        where
          realized = null . unrealized
          refines _ Nothing _ =
              error "Cohort.specialization: cannot find point of view"
          refines k (Just k') mapping =
              not $ null $ homomorphism k' k mapping

{--  Debugging apparatus:

          showSome k'' v =
              if (5 == L.length (insts k)) && (1+L.length (insts k'') == L.length (insts k)
                                              && null (unrealized k''))
              then
                  (z
                   ("length: " ++ (show (L.length (insts k''))) ++
--                    ", unrealized: " ++ (show (unrealized k'')) ++
--                    ", prev nodes: " ++ (show (addSendingBefore S.empty (vertex k'' (0,0)))) ++
                    ", map: " ++ (show (getStrandMap (operation k''))) ++
                    ", prob: " ++ (show (prob k'')) ++
                    ", POV OK: " ++ (show (refines k'' (pov k'') (prob k''))) ++
                    ", refines: " ++ (show (refines k (Just k'') mapping)) ++
                    ", survives: " ++
                    (show ((realized k'') &&  (not (isomorphic (gist k) (gist k''))) &&
                           (refines k'' (pov k'') (prob k'')) &&
                           (refines k (Just k'') mapping))))
                   v)
              else v

--          maybeOK x = if (12 < L.length (insts k)) then z "OK" x else x
--}
