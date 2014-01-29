-- Converts a solution to a problem into a coherent logic formula

-- Copyright (c) 2011 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Logic.Logic (Prot, Preskel, State, logic) where

import qualified Data.List as L
import CPSA.Lib.CPSA

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

type State t g c = ([Prot t g c], [Preskel t g c])

logic :: (Algebra t p g s e c, Monad m) => String -> g ->
         State t g c -> Maybe (SExpr Pos) ->
         m (State t g c, Maybe (SExpr ()))
logic _ _ (ps, ks) Nothing =    -- Nothing signifies end-of-file
    displayFormula ps (reverse ks)
logic name gen (ps, []) (Just sexpr) = -- Looking for POV skeleton
    loadPOV name gen ps sexpr
logic name gen (ps, ks) (Just sexpr) = -- Looking for shapes
    loadOtherPreskel name gen ps ks sexpr

loadPOV :: (Algebra t p g s e c, Monad m) => String -> g ->
           [Prot t g c] -> SExpr Pos ->
           m (State t g c, Maybe (SExpr ()))
loadPOV name origin ps (L pos (S _ "defprotocol" : xs)) =
    do
      p <- loadProt name origin pos xs
      return ((p : ps, []), Nothing)
loadPOV _ _ ps (L pos (S _ "defskeleton" : xs)) =
    do
      p <- findProt pos ps xs
      k <- loadPreskel pos p (pgen p) emptyContext xs
      case (isSkeleton k, isShape k) of
        (True, False) -> return ((ps, [k]), Nothing) -- Found POV
        _ -> return ((ps, []), Nothing)              -- Not POV
loadPOV _ _ ps _ = return ((ps, []), Nothing)

loadOtherPreskel :: (Algebra t p g s e c, Monad m) => String -> g ->
                    [Prot t g c] -> [Preskel t g c] ->
                    SExpr Pos -> m (State t g c, Maybe (SExpr ()))
loadOtherPreskel name origin ps ks (L pos (S _ "defprotocol" : xs)) =
    do                     -- Found next protocol.  Print this formula
      p <- loadProt name origin pos xs
      displayFormula (p : ps) (reverse ks)
loadOtherPreskel _ _ ps ks (L pos (S _ "defskeleton" : xs)) =
    do
      p <- findProt pos ps xs
      let g = kgen (last ks)    -- Make sure vars in skeleton are
      let c = kctx (last ks)    -- distinct from the ones in the POV
      k <- loadPreskel pos p g c xs
      case isShape k of
        True -> return ((ps, k : ks), Nothing) -- Found shape
        False -> return ((ps, ks), Nothing) -- Found intermediate skeleton
loadOtherPreskel _ _ ps ks _ = return ((ps, ks), Nothing)

-- Load a protocol

-- The Prot record contains information extraced from protocols for
-- use when processing preskeletons.  A protocol includes a role for
-- all listeners.
data Prot t g c = Prot
    { pname :: String,          -- Protocol name
      pgen :: g,                -- Generator for preskeletons
      roles :: [Role t c] }
    deriving Show

-- The Role record contains information extraced from roles for use
-- when processing preskeletons.
data Role t c = Role
    { rname :: String,          -- Role name
      vars :: [t],
      ctx :: c }
    deriving Show

-- Load a protocol.  On success, returns a Prot record.

loadProt :: (Algebra t p g s e c, Monad m) => String -> g ->
            Pos -> [SExpr Pos] -> m (Prot t g c)
loadProt nom origin pos (S _ name : S _ alg : x : xs)
    | alg /= nom =
        fail (shows pos $ "Expecting terms in algebra " ++ nom)
    | otherwise =
        do
          (gen, rs) <- loadRoles origin (x : xs)
          (gen', r) <- makeListenerRole pos gen
          return (Prot { pname = name, pgen = gen', roles = r : rs })
loadProt _ _ pos _ =
    fail (shows pos "Malformed protocol")

-- A generator is threaded thoughout the protocol loading process so
-- as to ensure no variable occurs in two roles.  It also ensures that
-- every variable that occurs in a preskeleton never occurs in one of
-- its roles.

loadRoles :: (Algebra t p g s e c, Monad m) => g ->
             [SExpr Pos] -> m (g, [Role t c])
loadRoles origin xs =
    mapAccumLM loadRole origin $ stripComments xs

stripComments :: [SExpr Pos] -> [SExpr Pos]
stripComments xs =
    filter pred xs
    where
      pred (L _ (S _ sym : _)) = sym == "defrole"
      pred _ = True             -- Catch bad entries

-- A monad version of map accumulation from the left
mapAccumLM :: Monad m => (a -> b -> m (a, c)) -> a -> [b] -> m (a, [c])
mapAccumLM _ z [] =
    return (z, [])
mapAccumLM f z (x : xs) =
    do
      (z', y) <- f z x
      (z'', ys) <- mapAccumLM f z' xs
      return (z'', y : ys)

loadRole :: (Algebra t p g s e c, Monad m) => g ->
            SExpr Pos -> m (g, Role t c)
loadRole gen (L _ (S _ "defrole" :
                     S _ name :
	             L _ (S _ "vars" : vars) :
                     L _ (S _ "trace" : _ : _) :
                     _)) =
    do
      (gen, vars) <- loadVars gen vars
      let ctx = addToContext emptyContext vars
      let r = Role { rname = name, vars = vars, ctx = ctx }
      return (gen, r)
loadRole _ x =
    fail (shows (annotation x) "Malformed role")

-- A protocol's listener role

listenerName :: String
listenerName = ""

makeListenerRole :: (Algebra t p g s e c, Monad m) => Pos -> g ->
                    m (g, Role t c)
makeListenerRole pos gen =
    do
      (gen', t) <- makeVar pos gen "x"
      let vars = [t]
      let ctx = addToContext emptyContext vars
      let r = Role { rname = listenerName, vars = vars, ctx = ctx }
      return (gen', r)

makeVar :: (Algebra t p g s e c, Monad m) => Pos -> g -> String -> m (g, t)
makeVar pos gen name =
    do
      (gen', ts) <- loadVars gen [L pos [S pos name, S pos "mesg"]]
      case ts of
        [t] -> return (gen', t)
        _ -> fail (shows pos "Bad variable generation")

-- Find a protocol

findProt :: (Algebra t p g s e c, Monad m) => Pos ->
            [Prot t g c] -> [SExpr Pos] -> m (Prot t g c)
findProt pos ps (S _ name : _) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> return p
findProt pos _ _ = fail (shows pos "Malformed skeleton")

-- Load a preskeleton

data Instance t c = Instance
    { pos :: Pos,               -- Instance position
      role :: Role t c,         -- Role from which this was instantiated
      env :: [(t, t)],          -- The environment
      height :: Int,            -- Height of the instance
      strand :: t }             -- Variable associated with the instance
    deriving Show

type Strands = [Int]            -- [Strand height]

type Node = (Int, Int)          -- (Strand, Position)

type Pair = (Node, Node)        -- Precedes relation

data Preskel t g c = Preskel
    { protocol :: Prot t g c,
      kgen :: g,                -- Final generator
      kvars :: [t],             -- Variables excluding strand vars
      insts :: [Instance t c],
      orderings :: [Pair],
      nons :: [t],
      uniqs :: [t],
      origs :: [(t, Node)],
      isSkeleton :: Bool,
      isShape :: !Bool,         -- Always looked at, so make it strict
      homomorphisms :: [SExpr Pos], -- Loaded later
      kctx :: c }

loadPreskel :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g c ->
               g -> c -> [SExpr Pos] -> m (Preskel t g c)
loadPreskel _ prot gen ctx (S _ _ : L _ (S _ "vars" : vars) : xs) =
    do
      (gen', kvars) <- loadVars gen vars
      (gen'', insts) <- loadInsts prot gen' kvars [] xs
      let strands = map strand insts
      let heights = map height insts
      orderings <- loadOrderings heights (assoc precedesKey xs)
      nons <- loadBaseTerms kvars (assoc nonOrigKey xs)
      uniqs <- loadBaseTerms kvars (assoc uniqOrigKey xs)
      origs <- loadOrigs kvars heights (assoc origsKey xs)
      let kctx = addToContext ctx (kvars ++ strands)
      return (Preskel { protocol = prot,
                        kgen = gen'',
                        kvars = kvars,
                        insts = insts,
                        orderings = orderings,
                        nons = nons,
                        uniqs = uniqs,
                        origs = origs,
                        isSkeleton = not $ hasKey preskeletonKey xs,
                        isShape = hasKey shapeKey xs,
                        homomorphisms = assoc mapsKey xs,
                        kctx = kctx })
loadPreskel pos _ _ _ _ = fail (shows pos "Malformed skeleton")

loadInsts :: (Algebra t p g s e c, Monad m) => Prot t g c ->
             g -> [t] -> [Instance t c] -> [SExpr Pos] -> m (g, [Instance t c])
loadInsts prot gen kvars insts (L pos (S _ "defstrand" : x) : xs) =
    case x of
      S _ role : N _ height : env ->
          do
            (gen', i) <- loadInst pos prot gen kvars role height env
            loadInsts prot gen' kvars (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrand")
loadInsts prot gen kvars insts (L pos (S _ "deflistener" : x) : xs) =
    case x of
      [term] ->
          do
            (gen', i) <- loadListener pos prot kvars gen term
            loadInsts prot gen' kvars (i : insts) xs
      _ ->
          fail (shows pos "Malformed deflistener")
loadInsts _ gen _ insts _ =
    return (gen, reverse insts)

loadInst :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g c ->
            g -> [t] -> String -> Int -> [SExpr Pos] -> m (g, Instance t c)
loadInst pos prot gen kvars role height env =
    do
      r <- lookupRole pos prot role
      env <- mapM (loadMaplet kvars (vars r)) env
      (gen', t) <- makeVar pos gen "z" -- Make the strand variable
      -- The sort of t will be fixed on output--see function skel.
      return (gen', Instance { pos = pos, role = r,
                               env = env, height = height,
                               strand = t })

lookupRole :: (Algebra t p g s e c, Monad m) => Pos ->
              Prot t g c -> String -> m (Role t c)
lookupRole pos prot role =
    case L.find (\r -> role == rname r) (roles prot) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname prot)
      Just r -> return r

loadMaplet :: (Algebra t p g s e c, Monad m) =>
              [t] -> [t] -> SExpr Pos -> m (t, t)
loadMaplet kvars vars (L _ [domain, range]) =
    do
      t <- loadTerm vars domain
      t' <- loadTerm kvars range
      return (t, t')
loadMaplet _ _ x = fail (shows (annotation x) "Malformed maplet")

loadListener :: (Algebra t p g s e c, Monad m) => Pos ->
                Prot t g c -> [t] -> g -> SExpr Pos -> m (g, Instance t c)
loadListener pos prot kvars gen x =
    do
      r <- lookupRole pos prot listenerName
      t <- loadTerm kvars x
      (gen', z) <- makeVar pos gen "z" -- Make the strand variable
      return (gen', Instance { pos = pos, role = r,
                               env = [(head $ vars r, t)], height = 2,
                               strand = z })

-- Load the node orderings

loadOrderings :: Monad m => Strands -> [SExpr Pos] -> m [Pair]
loadOrderings _ [] = return []
loadOrderings strands (x : xs) =
    do
      np <- loadPair strands x
      nps <- loadOrderings strands xs
      return (adjoin np nps)

loadPair :: Monad m => [Int] -> SExpr Pos -> m Pair
loadPair heights (L pos [x0, x1]) =
    do
      n0 <- loadNode heights x0
      n1 <- loadNode heights x1
      case sameStrands n0 n1 of  -- Same strand
        True -> fail (shows pos "Malformed pair -- nodes in same strand")
        False -> return (n0, n1)
    where
      sameStrands (s0, _) (s1, _) = s0 == s1
loadPair _ x = fail (shows (annotation x) "Malformed pair")

loadNode :: Monad m => [Int] -> SExpr Pos -> m Node
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

loadBaseTerms :: (Algebra t p g s e c, Monad m) => [t] -> [SExpr Pos] -> m [t]
loadBaseTerms _ [] = return []
loadBaseTerms vars (x : xs) =
    do
      t <- loadBaseTerm vars x
      ts <- loadBaseTerms vars xs
      return (adjoin t ts)

loadBaseTerm :: (Algebra t p g s e c, Monad m) => [t] -> SExpr Pos -> m t
loadBaseTerm vars x =
    do
      t <- loadTerm vars x
      case isAtom t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an atom")

loadOrigs :: (Algebra t p g s e c, Monad m) => [t] -> Strands ->
             [SExpr Pos] -> m [(t, Node)]
loadOrigs _ _ [] = return []
loadOrigs vars heights (x : xs) =
    do
      o <- loadOrig vars heights x
      os <- loadOrigs vars heights xs
      return (adjoin o os)

loadOrig :: (Algebra t p g s e c, Monad m) => [t] -> Strands ->
            SExpr Pos -> m (t, Node)
loadOrig vars heights (L _ [x, y]) =
    do
      t <- loadTerm vars x
      n <- loadNode heights y
      return (t, n)
loadOrig _ _ x =
    fail (shows (annotation x) "Malformed origination")

-- Homomorphisms

-- The maps entry in a preskeleton contains a list of homomorphisms.
-- A homomorphism is a list of length two, a strand map as a list of
-- natural numbers, and a substition.

loadMaps :: (Algebra t p g s e c, Monad m) => Preskel t g c ->
            Preskel t g c -> [SExpr Pos] -> m [[SExpr ()]]
loadMaps pov k maps =
    mapM (loadMap pov k) maps

loadMap :: (Algebra t p g s e c, Monad m) => Preskel t g c ->
            Preskel t g c -> SExpr Pos -> m [SExpr ()]
loadMap pov k (L _ [L _ strandMap, L _ algebraMap]) =
    do
      let zs = map strand $ insts pov
      perm <- mapM loadPerm strandMap -- Load the strand map
      let zs' = map strand $ insts k
      let zh = [(t, zs' !! p) | (t, p) <- zip zs perm]
      -- Compute the strand part of the homomorphism
      let eqs = map (displayEq $ kctx k) zh
      -- Load the algebra part of the homomorphism
      ah <- mapM (loadMaplet (kvars k) (kvars pov)) algebraMap
      -- Compute the algebra part of the homomorphism
      let eqa = map (displayEq $ kctx k) ah
      return (eqs ++ eqa)
loadMap _ _ x = fail (shows (annotation x) "Malformed map")

loadPerm :: Monad m => SExpr Pos -> m Int
loadPerm (N _ n) | n >= 0 = return n
loadPerm x = fail (shows (annotation x) "Expecting a natural number")

displayEq :: Algebra t p g s e c => c -> (t, t) -> SExpr ()
displayEq ctx (x, y) =
    L () [S () "equal", displayTerm ctx x, displayTerm ctx y]

-- Association lists

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr a] -> [SExpr a]
assoc key alist =
    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]

keyPred :: String -> SExpr a -> Bool
keyPred key (L _ (S _ head : _)) = key == head
keyPred _ _ = False

hasKey :: String -> [SExpr a] -> Bool
hasKey key alist = any (keyPred key) alist

-- The key used to identify a non-skeleton
preskeletonKey :: String
preskeletonKey = "preskeleton"

-- The key used to identify a shape
shapeKey :: String
shapeKey = "shape"

-- The key used to extract the list of homomorphisms
mapsKey :: String
mapsKey = "maps"

-- The key used in preskeletons for communication orderings
precedesKey :: String
precedesKey = "precedes"

-- The key used in preskeletons for non-originating atoms
nonOrigKey :: String
nonOrigKey = "non-orig"

-- The key used in preskeletons for uniquely originating atoms
uniqOrigKey :: String
uniqOrigKey = "uniq-orig"

-- The key used to extract the nodes of origination
origsKey :: String
origsKey = "origs"

-- Formula printing

displayFormula :: (Algebra t p g s e c, Monad m) =>
                  [Prot t g c] -> [Preskel t g c] ->
                  m (State t g c, Maybe (SExpr ()))
displayFormula ps [] =
    return ((ps, []), Nothing)
displayFormula ps (k : ks) =
    do
      sexpr <- form k ks
      return ((ps, []), Just sexpr)

form :: (Algebra t p g s e c, Monad m) => Preskel t g c ->
        [Preskel t g c] -> m (SExpr ())
form k ks =                     -- k is the POV skeleton
    do                          -- ks is the list of shapes
      (vars, conj) <- skel k
      disj <- mapM (shape k) ks
      return $ quantify "forall" vars
                 (imply (conjoin conj) (disjoin disj))

-- Convert one skeleton into a declaration and a conjunction.  The
-- declaration is used as the bound variables in a quantifier.
skel :: (Algebra t p g s e c, Monad m) => Preskel t g c ->
        m ([SExpr ()], [SExpr ()])
skel k =
    do
      let vars = displayVars (kctx k) (kvars k)
      let strands = displayVars (kctx k) (map strand $ insts k)
      return (vars ++ listMap nat strands,
              map (strandForm k) (insts k) ++
              map (precForm k) (orderings k) ++
              map (unary "non" $ kctx k) (nons k) ++
              map (unary "uniq" $ kctx k) (uniqs k) ++
              map (origForm k) (origs k))

listMap :: ([SExpr ()] -> [SExpr ()]) -> [SExpr ()] -> [SExpr ()]
listMap _ [] = []
listMap f (L () xs : ys) = L () (f xs) : listMap f ys
listMap f (y : ys) = y : listMap f ys

-- Replace "mesg" as the sort in the list with "nat"
nat :: [SExpr ()] -> [SExpr ()]
nat [] = error "Logic.nat: empty list as argument"
nat [_] = [S () "nat"]
nat (v : vs) = v : nat vs

-- Creates the atomic formulas used to describe an instance of a role
strandForm :: Algebra t p g s e c => Preskel t g c ->
              Instance t c -> SExpr ()
strandForm k inst =
    conjoin $ map f $ env inst
    where
      f (x, t) =
          L () [S () "strand",
                Q () $ pname $ protocol k, -- Name of the protocol
                Q () $ rname $ role inst, -- Name of the role
                N () $ height inst,
                quote $ displayTerm (ctx $ role inst) x,
                displayTerm (kctx k) (strand inst),
                displayTerm (kctx k) t]

quote :: SExpr () -> SExpr ()
quote (S () str) = Q () str
quote x = x

-- Creates the atomic formula used to describe a node ordering relation
precForm :: Algebra t p g s e c => Preskel t g c -> Pair -> SExpr ()
precForm k ((s, i), (s', i')) =
    L () [S () "prec",
          displayTerm (kctx k) t,
          N () i,
          displayTerm (kctx k) t',
          N () i']
    where
      t = strand $ insts k !! s
      t' = strand $ insts k !! s'

origForm :: Algebra t p g s e c => Preskel t g c ->
            (t, Node) -> SExpr ()
origForm k (t, (s, i)) =
    L () [S () "orig",
          displayTerm (kctx k) t,
          displayTerm (kctx k) z,
          N () i]
    where
      z = strand $ insts k !! s

-- Creates a formula associated with a shape.  It is a disjunction of
-- existentially quantified formulas that describe the homomorphism
-- and the shape as a skeleton.
shape :: (Algebra t p g s e c, Monad m) => Preskel t g c ->
         Preskel t g c -> m (SExpr ())
shape pov k =
    do
      (vars, conj) <- skel k
      case null $ homomorphisms k of
        True -> fail "No homomorphism for shape"
        False ->
            do
              hs <- loadMaps pov k (homomorphisms k)
              let xs = [quantify "exists" vars $ conjoin (h ++ conj) | h <- hs]
              return $ disjoin xs

-- Formula primitives

unary :: Algebra t p g s e c => String -> c -> t -> SExpr ()
unary pred ctx t =
    L () [S () pred, displayTerm ctx t]

quantify :: String -> [SExpr ()] -> SExpr () -> SExpr ()
quantify _ [] form = form
quantify name vars form =
    L () [S () name, L () vars, form]

conjoin :: [SExpr ()] -> SExpr ()
conjoin conjuncts =
    case concatMap f conjuncts of
      [x] -> x
      xs -> L () (S () "and" : xs)
    where
      f (L () (S () "and" : xs)) = xs
      f x = [x]

disjoin :: [SExpr ()] -> SExpr ()
disjoin conjuncts =
    case concatMap f conjuncts of
      [x] -> x
      xs -> L () (S () "or" : xs)
    where
      f (L () (S () "or" : xs)) = xs
      f x = [x]

imply :: SExpr () -> SExpr () -> SExpr ()
imply (L () [S () "and"]) consequence = consequence
imply antecedent consequence =
    L () [S () "implies", antecedent, consequence]
