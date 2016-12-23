-- Computes the cohort associated with a skeleton or its generalization

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Cohort (Mode(..), reduce, unrealized) where

import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.List as L
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Strand

{-- Debugging support
import System.IO.Unsafe

z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x

zn :: Show a => a -> Maybe b -> Maybe b
zn x Nothing = z x Nothing
zn _ y = y

zf :: Show a => a -> Bool -> Bool
zf x False = z x False
zf _ y = y

zt :: Algebra t p g s e c => [Term] -> String
zt t =
    show (displayTerm (addToContext emptyContext [t]) t)

zs :: Algebra t p g s e c => Set [Term] -> String
zs s =
    show $ map (displayTerm (addToContext emptyContext ts)) ts
    where
      ts = S.toList s

zi :: Algebra t p g s e c => Instance -> String
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
useEcapeSetInTargetTerms :: Bool
useEcapeSetInTargetTerms = False -- True

-- Filter a cohort for skeletons that solve the test.  Turn off only
-- to debug the other parts of the test solving algorithm.
useSolvedFilter :: Bool
useSolvedFilter = True -- False

-- Use thinning during generalization.
useThinningDuringGeneralization :: Bool
useThinningDuringGeneralization = False -- True

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
                let ns' = addSendingBefore ns n
                    ts = termsInNodes ns' in
                case derivable a ts t of
                  True -> (acc, ns')
                  False -> (graphNode n : acc, ns')

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

termsInNodes :: Set Vertex -> Set Term
termsInNodes ns =
  S.map (evtTerm . event) ns

-- Returns that atoms that cannot be guess when determining if a
-- term is derivable from some other terms, and the atoms that
-- uniquely originate in this skeleton.
avoid :: Preskel -> (Set Term, [Term])
avoid k =
    (S.unions [ns, as, us], L.nub ((kpnon k) ++ u))
    where
      ns = S.fromList (knon k)
      as = S.fromList (kpnon k)
      u = uniqOrig k
      us = S.fromList u

-- Suppose k --v,p-> k', where k |-phi,sigma-> k'.  Let t=msg(k, v)@p,
-- t'=sigma(t), T=sigma(esc(k, v, t)), and t"=msg(k', phi(v)).
-- Position p is solved in k' from k at v if:
--
-- 1. some member of anc(t", p) is in T', or
--
-- 2. for some t in outpred(k', phi(v)), t' is not carried only within
--    T in t, or
--
-- 3. targetterms(t', T) \ sigma(targetterms(t, esc(k, v, t)) /= empty
--    and there are variables in k's protocol that are not atoms, or
--
-- 4. the decryption key for an element of T is derivable, or
--
-- 5. t' is an encryption and the encryption key for t' is derivable.
--
-- Haskell variables:
-- ct     = t
-- pos    = p
-- ek     = encription key if ct is an encyption else nothing
-- escape = esc(k, v, t)
-- k      = k
-- (s, p) = v and n
-- subst  = sigma
solved :: Term -> Place -> [Term] -> Set Term ->
          Preskel -> Node -> Subst -> Bool
solved ct pos eks escape k (s, p) subst =
    -- Condition 1
    isAncestorInSet escape' t pos ||
    -- Condition 2
    any (not . carriedOnlyWithin ct' escape') (S.toList ts) ||
    -- Condition 3
    not (varsAllAtoms (protocol k)) && not (S.null targetTermsDiff) ||
    -- Condition 4
    any (maybe False (derivable a ts) . decryptionKey) (S.toList escape') ||
    -- Condition 5
    -- Bug fix: apply subst to eks
    any (derivable a ts) (map (substitute subst) eks)
    where
      v = vertex k (s, p)       -- Look up vertex in k
      t = evt id erro (event v)  -- Term at v
      erro = const $ error "Cohort.solved: got an outbound term"
      ct' = substitute subst ct -- Mapped critical term
      escape' = S.map (substitute subst) escape
      mappedTargetTerms = S.map (substitute subst) (targetTerms ct escape)
      targetTermsDiff = S.difference (targetTerms ct' escape') mappedTargetTerms
      vs = addSendingBefore S.empty v
      ts = termsInNodes  vs     -- Outbound predecessors
      (a, _) = avoid k

maybeSolved :: Term -> Place -> [Term] -> Set Term ->
               Preskel -> Node -> Subst -> Bool
maybeSolved ct pos eks escape k n subst =
    not useSolvedFilter || solved ct pos eks escape k n subst

data Mode = Mode
    { noGeneralization :: Bool,
      nonceFirstOrder :: Bool,
      visitOldStrandsFirst :: Bool,
      reverseNodeOrder :: Bool }
    deriving Show

-- Abort if there is an unrealized node without a test, otherwise
-- return a list of skeletons that solve one test.  If the skeleton is
-- realized, try to generalize it, but only when noIsoChk is false.
reduce :: Mode -> Preskel -> [Preskel]
reduce mode k =
    maybe (whenRealized k) id (findTest mode k u a)
    where
      (a, u) = avoid k
      whenRealized k =
          if noGeneralization mode then [] else maximize k

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
                let ns = addSendingBefore S.empty n
                    ts = termsInNodes ns    -- Public messages
                    (ts', a') = decompose ts a in
                if buildable ts' a' t then
                    loop nodes
                else
                    Just $ testNode mode k u ts' a' (graphNode n) t

-- Look for a critical term that makes this node a test node.
testNode :: Mode -> Preskel -> [Term] -> Set Term -> Set Term ->
            Node -> Term -> [Preskel]
testNode mode k u ts a n t =
    loop cts
    where
      loop [] = error (
        "Cohort.testNode missing test at " ++ show n ++ "\n" ++ show t)
      loop ((ct, eks) : cts) =
          case escapeSet ts a ct of
            Nothing -> loop cts
            Just escape ->
                places (carriedPlaces ct t)
                where
                  places [] = loop cts -- Find position at which
                  places (p : ps)      -- ct has escaped
                      | isAncestorInSet escape t p = places ps
                      | otherwise = solveNode k ct p eks n t escape
      cts =                     -- Potential critical messages
          if nonceFirstOrder mode then
              map f (filter (flip carriedBy t) u) ++
              filter g (map h (encryptions t))
          else
              filter g (map h (encryptions t)) ++
              map f (filter (flip carriedBy t) u)
      f ct = (ct, [])           -- A nonce tests has no eks
      g (_, []) = False         -- An encryption test must have
      g _ = True                -- at least one non-derivable key
      -- Dump derivable encryption keys
      h (ct, eks) = (ct, filter (not . buildable ts a) eks)

carriedOnlyWithin :: Term -> Set Term -> Term -> Bool
carriedOnlyWithin target escape source =
    all (isAncestorInSet escape source) (carriedPlaces target source)

-- isAncestorInSet set source position is true if there is one ancestor of
-- source at position that is in the set.
isAncestorInSet :: Set Term -> Term -> Place -> Bool
isAncestorInSet set source position =
    any (flip S.member set) (ancestors source position)

-- Solve critical message at position pos at node n.
-- ct = t @ pos
-- t  = msg(k, n)
solveNode :: Preskel -> Term -> Place -> [Term] -> Node -> Term ->
             Set Term -> [Preskel]
solveNode k ct pos eks n t escape =
    mgs $ cons ++ augs ++ lsns
    where
      cons = contractions k ct pos eks n t escape cause
      augs = augmentations k ct pos eks n escape cause
      lsns = addListeners k ct pos eks n t escape cause
      cause = Cause (dir eks) n ct escape

-- Filter out all but the skeletons with the most general homomorphisms.

mgs :: [(Preskel, [Sid])] -> [Preskel]
mgs cohort =
  reverse $ map fst $ loop cohort []
  where
    loop [] acc = acc
    loop (kphi : cohort) acc
      | any (f kphi) cohort || any (f kphi) acc =
        loop cohort acc
      | otherwise = loop cohort (kphi : acc)
    f (k, phi) (k', phi') =
      any (not. null . homomorphism k' k)
          (composeFactors (strandids k) (strandids k') phi phi')

-- Given two permutations p and p', with ranges r and r', this
-- function returns the list of permutations p'' such that
--
--    p'' o p' = p.
--
-- This function assumes p' is injective and the returns permutations
-- that also must be.

composeFactors :: [Int] -> [Int] -> [Int] -> [Int] -> [[Int]]
composeFactors r r' p p' =
  perms (zip p' p) (filter (flip notElem p) r) r'

-- The correctness of this function depends on the fact that the
-- length of range is at most one so that the result is always
-- injective.

perms :: [(Int, Int)] -> [Int] -> [Int] -> [[Int]]
perms _ _ [] = [[]]
perms alist range (s:domain) =
  case lookup s alist of
    Just s' -> [ s':ss | ss <- perms alist range domain ]
    Nothing -> [ s':ss | s' <- range, ss <- perms alist range domain ]

-- Contractions

-- Contract the critical message at the given position.
contractions :: Preskel -> Term -> Place -> [Term] -> Node -> Term ->
                Set Term -> Cause -> [(Preskel, [Sid])]
contractions k ct pos eks n t escape cause =
    [ (k, phi) |
          let anc = ancestors t pos,
          subst <- solve escape anc (gen k, emptySubst),
          (k, n, phi, subst') <- contract k n cause subst,
          maybeSolved ct pos eks escape k n subst' ]

solve :: Set Term -> [Term] -> (Gen, Subst) -> [(Gen, Subst)]
solve escape ancestors subst =
    [ s | e <- S.toList escape,
          a <- ancestors,
          s <- unify a e subst ]

carriedOnlyWithinAtSubst :: Term -> Set Term -> Term -> (Gen, Subst) -> Bool
carriedOnlyWithinAtSubst  ct escape t (_, subst) =
    carriedOnlyWithin ct' escape' t'
    where
      ct' = substitute subst ct
      escape' = S.map (substitute subst) escape
      t' = substitute subst t

fold :: Term -> Set Term -> Term -> (Gen, Subst) -> [(Gen, Subst)]
fold ct escape t (gen, subst) =
    [ (gen', compose subst' subst) |
      (gen', subst') <- foldl f [(gen, emptySubst)] (carriedPlaces ct' t') ]
    where
      ct' = substitute subst ct
      escape' = S.map (substitute subst) escape
      t' = substitute subst t
      f substs p =
          [ s | subst <- substs, s <- solve escape' (ancestors t' p) subst ]

dir :: [a] -> Direction
dir [] = Nonce
dir _ = Encryption

-- Augmentations

augmentations :: Preskel -> Term -> Place -> [Term] -> Node -> Set Term ->
                 Cause -> [(Preskel, [Sid])]
augmentations k ct pos eks n escape cause =
    [ k' | r <- roles (protocol k),
           k' <- roleAugs k ct pos eks n escape cause targets r ]
    where
      targets = S.toList (targetTerms ct escape)

roleAugs :: Preskel -> Term -> Place -> [Term] -> Node -> Set Term ->
            Cause -> [Term] -> Role -> [(Preskel, [Sid])]
roleAugs k ct pos eks n escape cause targets role =
    [ (k', phi) |
           (subst', inst) <-
               transformingNode ct escape targets role subst,
           (k', n', phi, subst'') <-
               augment k n cause role subst' inst,
           maybeSolved ct pos eks escape k' n' subst'' ]
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

transformingNode :: Term -> Set Term -> [Term] -> Role ->
                    (Gen, Subst) -> [((Gen, Subst), Instance)]
transformingNode ct escape targets role subst =
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
            acc' = maybeAug ct escape role ht substs' acc t

-- Terms considered for binding with the carried terms in an outbound
-- term.
targetTerms :: Term -> Set Term -> Set Term
targetTerms ct escape =
    if useEcapeSetInTargetTerms then
       targetTermsWithEscapeSet
    else
       S.difference targetTermsWithEscapeSet escape
    where
      targetTermsWithEscapeSet = S.fold f (S.singleton ct) escape
      f t ts =
          foldl (flip S.insert) ts
                (concatMap (ancestors t) (carriedPlaces ct t))

-- Find bindings for terms in the test.
carriedBindings :: [Term] -> Term -> (Gen, Subst) -> [(Gen, Subst)]
carriedBindings targets outbound subst =
    [ s |
      subterm <- S.toList (foldCarriedTerms (flip S.insert) S.empty outbound),
      target <- targets,
      s <- unify subterm target subst ]

-- Ensure the critical term is carried only within the escape set of
-- every term in the past using fold from cows.
cowt :: Term -> Set Term -> Trace -> [(Gen, Subst)] -> [(Gen, Subst)]
cowt ct escape c substs =
    nubSnd $ concatMap (cowt0 ct escape c) substs

-- Remove pairs with the same second element.
nubSnd :: Eq b => [(a, b)] -> [(a, b)]
nubSnd substs =
    L.nubBy (\(_, s) (_, s') -> s == s') substs

-- Handle one substitution at a time.
cowt0 :: Term -> Set Term -> Trace -> (Gen, Subst) -> [(Gen, Subst)]
cowt0 ct escape c subst =
    if all (f subst) c then     -- Substitution works
        [subst]
    else                        -- Substitution needs refinement
        cowt ct escape c (foldn ct escape c [subst])
    where
      f subst evt =
          carriedOnlyWithinAtSubst ct escape (evtTerm evt) subst

-- Apply fold to each message in the trace.
foldn :: Term -> Set Term -> Trace -> [(Gen, Subst)] -> [(Gen, Subst)]
foldn _ _ [] substs = substs
foldn ct escape (evt : c) substs =
    foldn ct escape c (concatMap (fold ct escape (evtTerm evt)) substs)

-- If the outbound term is carried only within, no transforming node
-- was found, otherwise, add a candidate augmentation to the
-- accumulator.
maybeAug :: Term -> Set Term -> Role -> Int -> [(Gen, Subst)] ->
            [((Gen, Subst), Instance)] -> Term ->
            [((Gen, Subst), Instance)]
maybeAug ct escape role ht substs acc t =
    foldl f acc $ L.filter testNotSolved substs
    where
      testNotSolved (_, subst) =
          not $ carriedOnlyWithin
                  (substitute subst ct)
                  (S.map (substitute subst) escape)
                  (substitute subst t)
      f acc (gen, subst) =
          case bldInstance role itrace gen of
            (gen, inst) : _ -> ((gen, subst), inst) : acc
            [] -> acc
          where
            itrace = map (evtMap $ substitute subst) (take ht (rtrace role))

-- Listener augmentations

addListeners :: Preskel -> Term -> Place -> [Term] -> Node -> Term ->
                Set Term -> Cause -> [(Preskel, [Sid])]
addListeners k ct pos eks n t escape cause =
    [ (k', phi) |
           t' <- filter (/= t) (S.toList (escapeKeys eks escape)),
           (k', n', phi, subst) <- addListener k n cause t',
           maybeSolved ct pos eks escape k' n' subst ]

escapeKeys :: [Term] -> Set Term -> Set Term
escapeKeys eks escape =
    S.fold f es escape
    where
      f e s = maybe s (flip S.insert s) (decryptionKey e)
      es = S.fromList eks

-- Maximize a realized skeleton if possible

maximize :: Preskel -> [Preskel]
maximize k =
    take 1 gens                 -- Return at most the first answer
    where
      gens = do
        (k', mapping) <- generalize k -- Generalize generates candidates
        specialization k k' mapping   -- Test a candidate

-- Test to see if realized skeleton k is a specialization of
-- preskeleton k' using the given strand mapping.  Returns the
-- skeleton associated with k' if it refines k.

specialization :: Preskel -> Preskel -> [Sid] -> [Preskel]
specialization k k' mapping
    | not (preskelWellFormed k') = []
    | otherwise =
        do
          k'' <- toSkeleton useThinningDuringGeneralization k'
          case realized k'' && not (isomorphic (gist k) (gist k'')) &&
               refines k'' (pov k'') (prob k'') &&
               refines k (Just k') mapping of
            True -> [k'']
            False -> []
        where
          realized = null . unrealized
          refines _ Nothing _ =
              error "Cohort.specialization: cannot find point of view"
          refines k (Just k') mapping =
              not $ null $ homomorphism k' k mapping
