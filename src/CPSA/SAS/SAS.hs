-- Converts a solution to a problem into a coherent logic formula

-- Copyright (c) 2011 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.SAS.SAS (State, sas) where

import Control.Monad (foldM)
import qualified Data.List as L
import qualified Data.Map as M
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Algebra

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

-- The root used for generated node names.
root :: String
root = "z"

type State = ([Prot], [Preskel])

sas :: MonadFail m => String -> Gen -> State -> Maybe (SExpr Pos) ->
       m (State, Maybe (SExpr ()))
sas _ _ (ps, ks) Nothing =    -- Nothing signifies end-of-file
    displayFormula ps (reverse ks)
sas name gen (ps, []) (Just sexpr) = -- Looking for POV skeleton
    loadPOV name gen ps sexpr
sas name gen (ps, ks) (Just sexpr) = -- Looking for shapes
    loadOtherPreskel name gen ps ks sexpr

loadPOV :: MonadFail m => String -> Gen -> [Prot] -> SExpr Pos ->
           m (State, Maybe (SExpr ()))
loadPOV name origin ps (L pos (S _ "defprotocol" : xs)) =
    do
      p <- loadProt name origin pos xs
      return ((p : ps, []), Nothing)
loadPOV _ _ ps (L pos (S _ "defskeleton" : xs)) =
    do
      p <- findProt pos ps xs
      k <- loadPreskel pos p (pgen p) xs
      case isFringe k of
        False -> return ((ps, [k]), Nothing) -- Found POV
        _ -> return ((ps, []), Nothing) -- Not POV
loadPOV _ _ ps _ = return ((ps, []), Nothing)

loadOtherPreskel :: MonadFail m => String -> Gen -> [Prot] -> [Preskel] ->
                    SExpr Pos -> m (State, Maybe (SExpr ()))
loadOtherPreskel name origin ps ks (L pos (S _ "defprotocol" : xs)) =
    do                     -- Found next protocol.  Print this formula
      p <- loadProt name origin pos xs
      displayFormula (p : ps) (reverse ks)
loadOtherPreskel _ _ ps ks (L pos (S _ "defskeleton" : xs)) =
    do
      p <- findProt pos ps xs
      let g = kgen (last ks)      -- Make sure vars in skeleton are
      k <- loadPreskel pos p g xs -- distinct from the ones in the POV
      case isFringe k of
        True -> return ((ps, k : ks), Nothing) -- Found shape
        False -> return ((ps, ks), Nothing) -- Found intermediate skeleton
loadOtherPreskel _ _ ps ks _ = return ((ps, ks), Nothing)

-- Load a protocol

-- The Prot record contains information extraced from protocols for
-- use when processing preskeletons.  A protocol includes a role for
-- all listeners.
data Prot = Prot
    { pname :: String,          -- Protocol name
      pgen :: Gen,                -- Generator for preskeletons
      roles :: [Role] }
    deriving Show

-- The Role record contains information extraced from roles for use
-- when processing preskeletons.
data Role = Role
    { rname :: String,          -- Role name
      vars :: [Term],
      ctx :: Context }
    deriving Show

-- Load a protocol.  On success, returns a Prot record.

loadProt :: MonadFail m => String -> Gen -> Pos -> [SExpr Pos] -> m (Prot)
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

loadRoles :: MonadFail m => Gen -> [SExpr Pos] -> m (Gen, [Role])
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

loadRole :: MonadFail m => Gen -> SExpr Pos -> m (Gen, Role)
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

makeListenerRole :: MonadFail m => Pos -> Gen -> m (Gen, Role)
makeListenerRole pos gen =
    do
      (gen', t) <- makeVar pos gen "x"
      let vars = [t]
      let ctx = addToContext emptyContext vars
      let r = Role { rname = listenerName, vars = vars, ctx = ctx }
      return (gen', r)

makeVar :: MonadFail m => Pos -> Gen -> String -> m (Gen, Term)
makeVar pos gen name =
    do
      (gen', ts) <- loadVars gen [L pos [S pos name, S pos "mesg"]]
      case ts of
        [t] -> return (gen', t)
        _ -> fail (shows pos "Bad variable generation")

-- Strand to variable maps

-- A variable map maps strands to variables

type VM = M.Map Strand Term

-- A generator and a variable map
type GVM = (Gen, VM)

-- Add a variable for a strand if the mapping does not already exist.
addVar :: MonadFail m => Pos -> GVM -> Strand -> m GVM
addVar pos (gen, vm) z =
  case M.lookup z vm of
    Just _ -> return (gen, vm)
    Nothing ->
      do
        (gen, t) <- makeVar pos gen root -- Make the variable
        return (gen, M.insert z t vm)

-- Strand lookup assumes a strand will always be found.
slookup :: Strand -> VM -> Term
slookup z vm =
  case M.lookup z vm of
    Just t -> t
    Nothing -> error ("SAS.slookup: cannot find " ++ show z)

nlookup :: Node -> VM -> (Term, Int)
nlookup (z, i) vm = (slookup z vm, i)

-- Find a protocol

findProt :: MonadFail m => Pos -> [Prot] -> [SExpr Pos] -> m Prot
findProt pos ps (S _ name : _) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> return p
findProt pos _ _ = fail (shows pos "Malformed skeleton")

-- Load a preskeleton

data Instance = Instance
    { pos :: Pos,               -- Instance position
      role :: Role,           -- Role from which this was instantiated
      env :: [(Term, Term)],    -- The environment
      height :: Int }           -- Height of the instance
    deriving Show

type Strands = [Int]            -- [Strand height]

type Strand = Int

type Node = (Strand, Int)       -- (Strand, Position)

type Pair = (Node, Node)        -- Precedes relation

type Fact = (String, [Term])

data Preskel = Preskel
    { protocol :: Prot,
      kgen :: Gen,                -- Final generator
      kvars :: [Term],            -- Algebra variables
      kstrands :: [Term],         -- Strand variables
      insts :: [Instance],
      strands :: [Term],        -- A variable for each instance
      orderings :: [((Term, Int), (Term, Int))],
      nons :: [Term],
      pnons :: [Term],
      uniqs :: [Term],
      origs :: [(Term, (Term, Int))],
      auths :: [Term],
      confs :: [Term],
      facts :: [Fact],
      isFringe :: !Bool,         -- Always looked at, so make it strict
      homomorphisms :: [SExpr Pos], -- Loaded later
      varmap :: VM }

loadPreskel :: MonadFail m => Pos -> Prot -> Gen -> [SExpr Pos] -> m (Preskel)
loadPreskel pos prot gen (S _ _ : L _ (S _ "vars" : vars) : xs) =
    do
      (gen, kvars) <- loadVars gen vars
      insts <- loadInsts prot kvars [] xs
      let heights = map height insts
      orderings <- loadOrderings heights (assoc precedesKey xs)
      nons <- loadBaseTerms kvars (assoc nonOrigKey xs)
      pnons <- loadBaseTerms kvars (assoc pnonOrigKey xs)
      uniqs <- loadBaseTerms kvars (assoc uniqOrigKey xs)
      origs <- loadOrigs kvars heights (assoc origsKey xs)
      auths <- loadBaseTerms kvars (assoc authKey xs)
      confs <- loadBaseTerms kvars (assoc confKey xs)
      (gen, varmap) <- makeVarmap pos gen [0..(length insts)-1]
      facts <- mapM (loadFact kvars varmap) (assoc factsKey xs)
      let f (n0, n1) = (nlookup n0 varmap, nlookup n1 varmap)
      let g (t, n) = (t, nlookup n varmap)
      return (Preskel { protocol = prot,
                        kgen = gen,
                        kvars = kvars,
                        kstrands = M.elems varmap,
                        insts = insts,
                        strands = M.elems varmap,
                        orderings = map f orderings,
                        nons = nons,
                        pnons = pnons,
                        uniqs = uniqs,
                        origs = map g origs,
                        auths = auths,
                        confs = confs,
                        facts = facts,
                        isFringe = hasKey shapeKey xs || hasKey fringeKey xs,
                        homomorphisms = assoc mapsKey xs,
                        varmap = varmap})
loadPreskel pos _ _ _ = fail (shows pos "Malformed skeleton")

loadInsts :: MonadFail m => Prot -> [Term] -> [Instance] ->
             [SExpr Pos] -> m [Instance]
loadInsts prot kvars insts (L pos (S _ "defstrand" : x) : xs) =
    case x of
      S _ role : N _ height : env ->
          do
            i <- loadInst pos prot kvars role height env
            loadInsts prot kvars (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrand")
loadInsts prot kvars insts (L pos (S _ "deflistener" : x) : xs) =
    case x of
      [term] ->
          do
            i <- loadListener pos prot kvars term
            loadInsts prot kvars (i : insts) xs
      _ ->
          fail (shows pos "Malformed deflistener")
loadInsts _ _ insts _ =
    return (reverse insts)

loadInst :: MonadFail m => Pos -> Prot -> [Term] -> String -> Int ->
            [SExpr Pos] -> m Instance
loadInst pos prot kvars role height env =
    do
      r <- lookupRole pos prot role
      env <- mapM (loadMaplet kvars (vars r)) env
      return (Instance { pos = pos, role = r,
                         env = env, height = height })

lookupRole :: MonadFail m => Pos -> Prot -> String -> m Role
lookupRole pos prot role =
    case L.find (\r -> role == rname r) (roles prot) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname prot)
      Just r -> return r

loadMaplet :: MonadFail m => [Term] -> [Term] -> SExpr Pos -> m (Term, Term)
loadMaplet kvars vars (L _ [domain, range]) =
    do
      t <- loadTerm vars domain
      t' <- loadTerm kvars range
      return (t, t')
loadMaplet _ _ x = fail (shows (annotation x) "Malformed maplet")

loadListener :: MonadFail m => Pos -> Prot -> [Term] -> SExpr Pos -> m Instance
loadListener pos prot kvars x =
    do
      r <- lookupRole pos prot listenerName
      t <- loadTerm kvars x
      return (Instance { pos = pos, role = r,
                         env = [(head $ vars r, t)], height = 2 })

-- Load the node orderings

loadOrderings :: MonadFail m => Strands -> [SExpr Pos] -> m [Pair]
loadOrderings _ [] = return []
loadOrderings strands (x : xs) =
    do
      np <- loadPair strands x
      nps <- loadOrderings strands xs
      return (adjoin np nps)

loadPair :: MonadFail m => [Int] -> SExpr Pos -> m Pair
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

loadBaseTerms :: MonadFail m => [Term] -> [SExpr Pos] -> m [Term]
loadBaseTerms _ [] = return []
loadBaseTerms vars (x : xs) =
    do
      t <- loadBaseTerm vars x
      ts <- loadBaseTerms vars xs
      return (adjoin t ts)

loadBaseTerm :: MonadFail m => [Term] -> SExpr Pos -> m Term
loadBaseTerm vars x =
    do
      t <- loadTerm vars x
      case isAtom t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting an atom")

loadOrigs :: MonadFail m => [Term] -> Strands -> [SExpr Pos] -> m [(Term, Node)]
loadOrigs _ _ [] = return []
loadOrigs vars heights (x : xs) =
    do
      o <- loadOrig vars heights x
      os <- loadOrigs vars heights xs
      return (adjoin o os)

loadOrig :: MonadFail m => [Term] -> Strands -> SExpr Pos -> m (Term, Node)
loadOrig vars heights (L _ [x, y]) =
    do
      t <- loadTerm vars x
      n <- loadNode heights y
      return (t, n)
loadOrig _ _ x =
    fail (shows (annotation x) "Malformed origination")

-- Make a variable for each strand
makeVarmap :: MonadFail m => Pos -> Gen -> [Strand] -> m GVM
makeVarmap pos g strands =
  foldM (addVar pos) (g, M.empty) strands

loadFact :: MonadFail m => [Term] -> VM -> SExpr Pos -> m Fact
loadFact vars varmap (L _ (S _ name : ft)) =
  do
    ft <- mapM (loadFactTerm vars varmap) ft
    return (name, ft)
loadFact _ _ x =
  fail (shows (annotation x) "Malformed fact")

loadFactTerm :: MonadFail m => [Term] -> VM -> SExpr Pos -> m Term
loadFactTerm _ varmap (N pos z) =
  case M.lookup z varmap of
    Just t -> return t
    Nothing -> fail $ shows pos ("Bad strand in fact: " ++ show z)
loadFactTerm vars _ x =
  loadTerm vars x

-- Homomorphisms

-- The maps entry in a preskeleton contains a list of homomorphisms.
-- A homomorphism is a list of length two, a strand map as a list of
-- natural numbers, and a substition.

type Hom = ([(Term, Term)], [(Term, Term)])

loadMaps :: MonadFail m => Preskel -> Preskel -> [SExpr Pos] -> m [Hom]
loadMaps pov k maps =
    mapM (loadMap pov k) maps

loadMap :: MonadFail m => Preskel -> Preskel -> SExpr Pos -> m Hom
loadMap pov k (L _ [L _ strandMap, L _ algebraMap]) =
    do
      perm <- mapM loadPerm strandMap -- Load the strand map
      nh <- mapM (loadStrandEq k perm) (M.assocs $ varmap pov)
      -- Load the algebra part of the homomorphism
      ah <- mapM (loadMaplet (kvars k) (kvars pov)) algebraMap
      return (nh, ah)
loadMap _ _ x = fail (shows (annotation x) "Malformed map")

loadPerm :: MonadFail m => SExpr Pos -> m Int
loadPerm (N _ n) | n >= 0 = return n
loadPerm x = fail (shows (annotation x) "Expecting a natural number")

-- Applies a strand permutation to a strand.
loadStrandEq :: MonadFail m => Preskel -> [Int] -> (Strand, Term) ->
                m (Term, Term)
loadStrandEq k perm (z, v) =
  do
    z <- index perm z
    return (v, slookup z (varmap k))

index :: MonadFail m => [a] -> Int -> m a
index (x : _) 0 = return x
index (_ : xs) i | i > 0 = index xs (i - 1)
index _ _ = fail "Bad strand map"

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

-- The key used to identify a shape
shapeKey :: String
shapeKey = "shape"

-- The key used to identify a non-shape fringe
fringeKey :: String
fringeKey = "fringe"

-- The key used to extract the list of homomorphisms
mapsKey :: String
mapsKey = "maps"

-- The key used in preskeletons for communication orderings
precedesKey :: String
precedesKey = "precedes"

-- The key used in preskeletons for non-originating atoms
nonOrigKey :: String
nonOrigKey = "non-orig"

-- The key used in preskeletons for penetrator non-originating atoms
pnonOrigKey :: String
pnonOrigKey = "pen-non-orig"

-- The key used in preskeletons for uniquely originating atoms
uniqOrigKey :: String
uniqOrigKey = "uniq-orig"

-- The key used in preskeletons for authenticated channels
authKey :: String
authKey = "auth"

-- The key used in preskeletons for confidential channels
confKey :: String
confKey = "conf"

-- The key used to extract the nodes of origination
origsKey :: String
origsKey = "origs"

-- The key used to extract facts
factsKey :: String
factsKey = "facts"

type Analysis = (Preskel, [(Hom, Preskel)])

loadAnalysis :: MonadFail m => Preskel -> [Preskel] -> m (Analysis)
loadAnalysis pov ks =
  do
    shapes <- mapM f ks
    return (pov, concat shapes)
  where
    f k =
      case null $ homomorphisms k of
        True -> fail "No homomorphism for shape"
        False ->
            do
              hs <- loadMaps pov k (homomorphisms k)
              return [(h, k) | h <- hs]

-- Eliminate trivial homomorphisms by substituting for the equality
-- throughout the analysis.

reduce :: Analysis -> Analysis
reduce (pov, shapes) =
  (pov, map (reduceShape pov) shapes)

reduceShape :: Preskel -> (Hom, Preskel) -> (Hom, Preskel)
reduceShape pov (homo, k) =
  (mapHom env homo, mapSkel env pov k)
  where
    env = snd $ head $ homoEnv (kgen k) homo

-- Compute a substition for equalities that equate two variables
-- of the same sort.
homoEnv :: Gen -> Hom -> [(Gen, Env)]
homoEnv g (a, n) = matchEqs (a ++ n) (g, emptyEnv)

matchEqs :: [(Term, Term)] -> (Gen, Env) -> [(Gen, Env)]
matchEqs [] env = [env]
matchEqs (eq:eqs) env =
  do
    e <- matchEq eq env
    matchEqs eqs e

matchEq :: (Term, Term) -> (Gen, Env) -> [(Gen, Env)]
matchEq (t, p) env
  | isVar p =                   -- Match fails if there
    case match p t env of       -- a sort mismatch
      [] -> [env]
      e -> e
  | otherwise = [env]           -- Fail if p is not a variable

-- Apply substitution and remove trival equations.
mapHom :: Env -> Hom -> Hom
mapHom env (a, n) =
  (f a, f n)
  where
    f eqs = [(p, t1) |
             (p, t0) <- eqs,
             let t1 = instantiate env t0,
             p /= t1]

mapInst :: Env -> Instance -> Instance
mapInst e inst =
  inst { env = map f (env inst) }
  where
    f (p, x) = (p, instantiate e x)

mapSkel :: Env -> Preskel -> Preskel -> Preskel
mapSkel env pov k =
  k { kvars = vs L.\\ kvars pov, -- Delete redundant POV variables
      kstrands = zs L.\\ kstrands pov,
      insts = map (mapInst env) (insts k),
      strands = zs,
      orderings = mapPair (instantiate env) (orderings k),
      nons = map (instantiate env) (nons k),
      pnons = map (instantiate env) (pnons k),
      uniqs = map (instantiate env) (uniqs k),
      origs = mapOrig (instantiate env) (origs k),
      auths = map (instantiate env) (auths k),
      confs = map (instantiate env) (confs k),
      facts = mapFact (instantiate env) (facts k),
      varmap = M.map (instantiate env) (varmap k) }
  where
    vs = map (instantiate env) (kvars k)
    zs = map (instantiate env) (kstrands k)
    mapNode f (z, i) = (f z, i)
    mapPair f l = map (\(a, b) -> (mapNode f a, mapNode f b)) l
    mapOrig f l = map (\(a, b) -> (f a, mapNode f b)) l
    mapFact f l = map (\(name, ft) -> (name, map f ft)) l

-- Formula printing

displayFormula :: MonadFail m => [Prot] -> [Preskel] ->
                  m (State, Maybe (SExpr ()))
displayFormula ps [] =
    return ((ps, []), Nothing)
displayFormula ps (k : ks) =
    do
      analysis <- loadAnalysis k ks
      return ((ps, []), Just $ form $ reduce analysis)

form :: Analysis -> SExpr ()
form (pov, shapes) =
  let (c, vars, conj) = skel emptyContext pov in
  let disj = map (shape c conj) shapes in
  L () [S () "defgoal", S () (pname $ protocol pov), -- Name of protocol
        quantify "forall" vars (imply (conjoin conj) (disjoin disj))]

-- Convert one skeleton into a declaration and a conjunction.  The
-- declaration is used as the bound variables in a quantifier.  The
-- context is extended so it can be used as input for another
-- skeleton.
skel :: Context -> Preskel -> (Context, [SExpr ()], [SExpr ()])
skel ctx k =
  let vars = kvars k ++ kstrands k in
  let kctx = addToContext ctx vars in
  let strds = displayVars kctx (kstrands k) in
  (kctx,
   displayVars kctx (kvars k) ++ listMap strd strds,
   map (lengthForm kctx k) (M.assocs (varmap k)) ++
   concatMap (paramForm kctx) (zip (strands k) $ insts k) ++
   map (precForm kctx) (orderings k) ++
   map (unary "non" kctx) (nons k) ++
   map (unary "pnon" kctx) (pnons k) ++
   map (unary "uniq" kctx) (noOrigUniqs k) ++
   map (uniqAtForm kctx) (origs k) ++
   map (unary "auth" kctx) (auths k) ++
   map (unary "conf" kctx) (confs k) ++
   map (factForm kctx) (facts k))

-- map through lists in an S-Expression.
listMap :: ([SExpr ()] -> [SExpr ()]) -> [SExpr ()] -> [SExpr ()]
listMap _ [] = []
listMap f (L () xs : ys) = L () (f xs) : listMap f ys
listMap f (y : ys) = y : listMap f ys

-- Replace "mesg" as the sort in the list with "strd"
strd :: [SExpr ()] -> [SExpr ()]
strd [] = error "SAS.strd: empty list as argument"
strd [_] = [S () "strd"]
strd (v : vs) = v : strd vs

-- Creates the atomic formulas used to describe an instance of a role
lengthForm :: Context -> Preskel -> (Strand, Term) -> SExpr ()
lengthForm c k (z, n) =
    L () [S () "p",
          Q () $ rname $ role inst,  -- Name of the role
          displayTerm c n,
          N () $ height inst]
    where
      inst = insts k !! z

quote :: SExpr () -> SExpr ()
quote (S () str) = Q () str
quote x = x

-- Creates the atomic formulas used to describe an instance of a role
paramForm :: Context -> (Term, Instance) -> [SExpr ()]
paramForm c (z, inst) =
    map f (env inst)
    where
      f (x, t) =
          L () [S () "p",
                Q () $ rname $ role inst,  -- Name of the role
                quote $ displayTerm (ctx $ role inst) x,
                displayTerm c z,
                displayTerm c t]

-- Creates the atomic formula used to describe a node ordering relation
precForm :: Context -> ((Term, Int), (Term, Int)) -> SExpr ()
precForm = quaternary "prec"

uniqAtForm :: Context -> (Term, (Term, Int)) -> SExpr ()
uniqAtForm = ternary "uniq-at"

factForm :: Context -> (String, [Term]) -> SExpr ()
factForm c (name, ft) =
  L () (S () "fact" : S () name : map (displayTerm c) ft)

-- Returns the uniqs that do not originate in k.
noOrigUniqs :: Preskel -> [Term]
noOrigUniqs k =
  [ t | t <- uniqs k, all (f t) (origs k) ]
  where
    f t (t', _) = t /= t'

-- Creates a formula associated with a shape.  It is a disjunction of
-- existentially quantified formulas that describe the homomorphism
-- and the shape as a skeleton.
shape :: Context -> [SExpr ()] -> (Hom, Preskel) -> SExpr ()
shape c pov ((nh, ah), shape) =
  let (ctx, vars, conj) = skel c shape in
  let n = map (displayEq ctx) nh in
  let a = map (displayEq ctx) ah in -- List diff on S-Exprs
  quantify "exists" vars (conjoin (n ++ a ++ (conj L.\\ pov)))

displayEq :: Context -> (Term, Term) -> SExpr ()
displayEq = binary "="

-- Formula primitives

unary :: String -> Context -> Term -> SExpr ()
unary pred ctx t =
    L () [S () pred, displayTerm ctx t]

binary :: String -> Context -> (Term, Term) -> SExpr ()
binary pred ctx (t0, t1) =
    L () [S () pred, displayTerm ctx t0, displayTerm ctx t1]

ternary :: String -> Context -> (Term, (Term, Int)) -> SExpr ()
ternary pred ctx (t0, (t1, i1)) =
    L () [S () pred, displayTerm ctx t0, displayTerm ctx t1, N () i1]

quaternary :: String -> Context -> ((Term, Int), (Term, Int)) -> SExpr ()
quaternary pred ctx ((t0, i0), (t1, i1)) =
    L () [S () pred, displayTerm ctx t0, N () i0, displayTerm ctx t1, N () i1]

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
      [] -> L () [S () "false"]
      [x] -> x
      xs -> L () (S () "or" : xs)
    where
      f (L () (S () "or" : xs)) = xs
      f x = [x]

imply :: SExpr () -> SExpr () -> SExpr ()
imply (L () [S () "and"]) consequence = consequence
imply antecedent consequence =
    L () [S () "implies", antecedent, consequence]
