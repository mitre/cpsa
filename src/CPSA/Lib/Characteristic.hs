-- Makes the characteristic skeleton of a security goal

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Characteristic (characteristic) where

import Control.Monad
import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal
import CPSA.Lib.Strand

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

-- Entry point.  Takes a position, a protocol, a variable generator, a
-- goal, and a skeleton comment and makes a skeleton or fails.  This
-- function extracts the anecedent and univesally quantified variable.
characteristic :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                  g -> Goal t -> [SExpr ()] -> m (Preskel t g s e)
characteristic pos prot g goal comment =
  equalsForm pos prot goal g (uvars goal) (antec goal) comment

-- Checks for equals in an antecedent and fails if it finds one.  One
-- could use unification to solve the equality, and then apply the
-- result to the remaining parts of the formula.
equalsForm :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g -> Goal t ->
              g -> [t] -> [AForm t] -> [SExpr ()] -> m (Preskel t g s e)
equalsForm pos _ _ _ _ as _ | any isEquals as =
  fail (shows pos "Equals not allowed in antecedent")
equalsForm pos prot goal g vars as comment =
  splitForm pos prot goal g vars as comment

isEquals :: AForm t -> Bool
isEquals (Equals _ _) = True
isEquals _ = False

-- Split the formula into instance formulas and skeleton formulas.
-- The instance formulas are used to generate the skeleton's
-- instances, and the skeleton formulas generate the rest.  Make the
-- instances, and then make the rest.
splitForm :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g -> Goal t ->
           g -> [t] -> [AForm t] -> [SExpr ()] -> m (Preskel t g s e)
splitForm pos prot goal g vars as comment =
  do
    (nmap, g, insts) <- mkInsts pos g is
    mkSkel pos prot goal g vars insts ks comment
  where                         -- is is the instance formulas and
    (is, ks) = L.partition instForm as -- ks is the skeleton formulas

-- Instance formulas are role predicates, parameter predicates, and
-- strand prec.
instForm :: AForm t -> Bool
instForm (RolePred _ _ _) = True
instForm (ParamPred _ _ _ _) = True
instForm (StrPrec _ _) = True
instForm _ = False

mkInsts :: (Algebra t p g s e c, Monad m) => Pos -> g ->
           [AForm t] -> m ([(t, Node)], g, [Instance t e])
mkInsts pos g as =
  do
    nri <- nodeRoleIndex pos as
    nss <- binNodes pos nri as
    (g, insts) <- foldInsts pos g as nri nss
    return (nodeMap nri nss, g, insts)

type RoleIndex t = (Role t, Int)

-- Computes a map from nodes to role-index pairs
nodeRoleIndex :: (Eq t, Monad m) => Pos -> [AForm t] -> m [(t, RoleIndex t)]
nodeRoleIndex pos as =
  foldM f [] as
  where
    f nri (RolePred r i n) =
      case lookup n nri of
        Nothing -> return ((n, (r, i)) : nri)
        Just _ -> fail (shows pos
                        "Node occurs in more than one role predicate")
    f nri _ = return nri

nriLookup :: Eq t => t -> [(t, RoleIndex t)] -> RoleIndex t
nriLookup n nri =
  case lookup n nri of
    Just ri -> ri
    Nothing -> error "Characteristic.nriLookup: Bad lookup"

binNodes :: (Eq t, Monad m) => Pos -> [(t, RoleIndex t)] ->
            [AForm t] -> m [[t]]
binNodes pos nri as =
  foldM f (map (\(x, _) -> [x]) nri) as
  where
    f nss (StrPrec n n')
      | i >= i' || rname r /= rname r' =
        fail (shows pos "Bad str-prec")
      | otherwise = return $ merge n n' nss
      where
        (r, i) = nriLookup n nri
        (r', i') = nriLookup n' nri
    f nss _ = return nss

merge :: Eq t => t -> t -> [[t]] -> [[t]]
merge n n' nss =
  (ns ++ ns') : L.delete ns (L.delete ns' nss)
  where
    ns = findl n nss
    ns' = findl n' nss

findl :: Eq t => t -> [[t]] -> [t]
findl n nss =
  case L.find (elem n) nss of
    Just ns -> ns
    Nothing -> error "Characteristic.findl: cannot find a node"

foldInsts :: (Algebra t p g s e c, Monad m) => Pos -> g -> [AForm t] ->
             [(t, RoleIndex t)] -> [[t]] -> m (g, [Instance t e])
foldInsts _ g _ _ [] = return (g, [])
foldInsts pos g as nri (ns : nss) =
  do
    (g, inst) <- mkInst pos g as nri ns
    (g, insts) <- foldInsts pos g as nri nss
    return (g, inst : insts)

mkInst :: (Algebra t p g s e c, Monad m) => Pos -> g -> [AForm t] ->
          [(t, RoleIndex t)] -> [t] -> m (g, Instance t e)
mkInst _ _ _ _ [] = error "Characteristic.mkInst: no nodes"
mkInst pos g as nri (n : ns)
  | h < 1 || h > length (rtrace r) =
    fail (shows pos "Bad height")
  | otherwise =
      do
        (g, env) <- foldM (mkMaplet pos r (n : ns)) (g, emptyEnv) as
        return (mkInstance g r env h)
  where
    (r, i) = nriLookup n nri
    -- The height (1 + max index)
    h = 1 + foldr f i ns
    f n i = max i (snd $ nriLookup n nri)

mkMaplet :: (Algebra t p g s e c, Monad m) => Pos -> Role t ->
            [t] -> (g, e) -> AForm t -> m (g, e)
mkMaplet pos role ns env (ParamPred r v n t)
  | elem n ns =
    if rname role == rname r then
      case match v t env of
        env : _ -> return env
        [] -> fail (shows pos "Domain does not match range")
    else
      fail (shows pos
            "Role in parameter pred differs from role position pred")
mkMaplet _ _ _ env _ = return env

nodeMap :: Eq t => [(t, RoleIndex t)] -> [[t]] -> [(t, Node)]
nodeMap nri nss =
  [ (n, (z, i)) |
    (z, ns) <- zip [0..] nss,
    n <- ns,
    let (_, i) = nriLookup n nri ]
    
mkSkel :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
          Goal t -> g -> [t] -> [Instance t e] -> [AForm t] ->
          [SExpr ()] -> m (Preskel t g s e)
mkSkel pos p gl g vars insts as comment =
  do
    let o = []
    let nr = []
    let ar = []
    let ur = []
    let (nr', ar', ur') = foldl addInstOrigs (nr, ar, ur) insts
    let prios = []
    let k = mkPreskel g p [gl] insts o nr' ar' ur' prios comment
    case termsWellFormed $ nr' ++ ar' ++ ur' ++ kterms k of
      False -> fail (shows pos "Terms in skeleton not well formed")
      True -> return ()
    case verbosePreskelWellFormed k of
      Return () -> return k
      Fail msg -> fail $ shows pos
                  $ showString "Skeleton not well formed: " msg

data ReturnFail a
    = Return a
    | Fail String

instance Monad ReturnFail where
    return = Return
    Fail l >>= _ = Fail l
    Return r >>= k = k r
    fail s = Fail s

addInstOrigs :: Algebra t p g s e c => ([t], [t], [t]) ->
                Instance t e -> ([t], [t], [t])
addInstOrigs (nr, ar, ur) i =
    (foldl (flip adjoin) nr $ inheritRnon i,
     foldl (flip adjoin) ar $ inheritRpnon i,
     foldl (flip adjoin) ur $ inheritRunique i)

