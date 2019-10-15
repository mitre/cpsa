-- Makes the characteristic skeleton of a security goal

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Characteristic (Conj, characteristic) where

import Control.Monad
import qualified Data.List as L
import CPSA.Lib.Utilities
import CPSA.Lib.ReturnFail
import CPSA.Lib.SExpr
import CPSA.Algebra
import CPSA.Protocol
import CPSA.Strand

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

type Conj = [(Pos, AForm)]

-- Entry point.  Takes a position, a protocol, a variable generator, a
-- goal, and a skeleton comment and makes a skeleton or fails.  This
-- function extracts the anecedent and univesally quantified variable.
characteristic :: MonadFail m => Pos -> Prot -> [Goal] -> Gen ->
                  Conj -> [SExpr ()] -> m Preskel
characteristic pos prot goals g antec comment =
  equalsForm pos prot goals g antec comment

-- Checks for equals in an antecedent and fails if it finds one.  One
-- could use unification to solve the equality, and then apply the
-- result to the remaining parts of the formula.
equalsForm :: MonadFail m => Pos -> Prot -> [Goal] -> Gen ->
              Conj -> [SExpr ()] -> m Preskel
equalsForm pos _ _ _ as _ | any isEquals as =
  fail (shows pos "Equals not allowed in antecedent")
equalsForm pos prot goals g as comment =
  splitForm pos prot goals g as comment

isEquals :: (Pos, AForm) -> Bool
isEquals (_, Equals _ _) = True
isEquals _ = False

-- Split the formula into instance formulas and skeleton formulas.
-- The instance formulas are used to generate the skeleton's
-- instances, and the skeleton formulas generate the rest.  Make the
-- instances, and then make the rest.
splitForm :: MonadFail m => Pos -> Prot -> [Goal] -> Gen ->
             Conj -> [SExpr ()] -> m Preskel
splitForm pos prot goals g as comment =
  do
    (nmap, g, insts) <- mkInsts g is
    mkSkel pos prot goals nmap g insts ks comment
  where                         -- is is the instance formulas and
    (is, ks) = L.partition instForm as -- ks is the skeleton formulas

-- Instance formulas are role length and parameter predicates.
instForm :: (Pos, AForm) -> Bool
instForm (_, Length _ _ _) = True
instForm (_, Param _ _ _ _ _) = True
instForm _ = False

-- Make the instances from the instance predicates

mkInsts :: MonadFail m => Gen -> Conj -> m ([(Term, Sid)], Gen, [Instance])
mkInsts g as =
  do
    srl <- strdRoleLength as    -- Compute role-length of each strand
    (g, insts) <- foldInsts g as srl -- Construct instances
    let strdMap = zip (map fst srl) [0..] -- Construct strand map
    return (strdMap, g, insts) -- Construct node map for later use

-- Computes a map from strands to roles and lengths
strdRoleLength :: MonadFail m => Conj -> m [(Term, (Role, Int))]
strdRoleLength as =
  foldM f [] as
  where
    f srl (pos, Length r z h) =
      case lookup z srl of
        Nothing -> return ((z, (r, h)) : srl)
        Just (r', h')
          | rname r' /= rname r ->
            fail (shows pos
                  "Strand occurs in more than one role length atom")
          | h <= h' -> return srl -- Use original binding
          | otherwise -> return ((z, (r, h)) : srl)
    f srl _ = return srl

-- Construct instances
foldInsts :: MonadFail m => Gen -> Conj -> [(Term, (Role, Int))] ->
             m (Gen, [Instance])
foldInsts g _ [] = return (g, [])
foldInsts g as ((z, (r, h)) : srs) =
  do
    (g, inst) <- mkInst g as z r h
    (g, insts) <- foldInsts g as srs
    return (g, inst : insts)

-- Construct an instance by extracting maplets from the parameter
-- predicates associated with the strand.
mkInst :: MonadFail m => Gen -> Conj -> Term -> Role -> Int -> m (Gen, Instance)
mkInst g as z r h =
  do
    (g, env) <- foldM (mkMaplet r z) (g, emptyEnv) as
    return (mkInstance g r env h)

-- Add match from a maplet
mkMaplet :: MonadFail m => Role -> Term -> (Gen, Env) ->
            (Pos, AForm) -> m (Gen, Env)
mkMaplet role z env (pos, Param r v _ z' t)
  | z == z' =
    if rname role == rname r then -- Ensure role matches the one
      case match v t env of       -- used to create instance
        env : _ -> return env
        [] -> fail (shows pos "Domain does not match range")
    else
      fail (shows pos
            "Role in parameter pred differs from role position pred")
mkMaplet _ _ env _ = return env

-- Use this lookup when lookup must succeed, that is when loader makes
-- the check.
nMapLookup :: (Term, Int) -> [(Term, Sid)] -> Node
nMapLookup (z, i) nmap =
  case lookup z nmap of
    Just s -> (s, i)
    Nothing -> error "Characteristic.nMapLookup: Bad lookup"

-- Create a skeleton given a list of instances

mkSkel :: MonadFail m => Pos -> Prot -> [Goal] -> [(Term, Sid)] ->
          Gen -> [Instance] -> Conj -> [SExpr ()] -> m Preskel
mkSkel pos p goals nmap g insts as comment =
  do
    let o = foldr (mkPrec nmap) [] as
    let nr = foldr mkNon [] as
    let ar = foldr mkPnon [] as
    let ur = foldr mkUniq [] as
    let cf = foldr mkConf [] as
    let au = foldr mkAuth [] as
    let (nr', ar', ur', cf', au') =
          foldl addInstOrigs (nr, ar, ur, cf, au) insts
    let fs = foldr (mkFact nmap) [] as
    let prios = []
    let k = mkPreskel g p goals insts o nr' ar' ur' cf' au' fs prios comment
    mapM_ (checkUniqAt nmap k) as
    case termsWellFormed $ nr' ++ ar' ++ ur' ++ kterms k of
      False -> fail (shows pos "Terms in skeleton not well formed")
      True -> return ()
    case verbosePreskelWellFormed k of
      Return () -> return k
      Fail msg -> fail $ shows pos
                  $ showString "Skeleton not well formed: " msg

addInstOrigs :: ([Term], [Term], [Term], [Term], [Term]) ->
                Instance -> ([Term], [Term], [Term], [Term], [Term])
addInstOrigs (nr, ar, ur, cf, au) i =
    (foldl (flip adjoin) nr $ inheritRnon i,
     foldl (flip adjoin) ar $ inheritRpnon i,
     foldl (flip adjoin) ur $ inheritRunique i,
     foldl (flip adjoin) au $ inheritRconf i,
     foldl (flip adjoin) cf $ inheritRauth i)

mkPrec :: [(Term, Sid)] -> (Pos, AForm) -> [Pair] -> [Pair]
mkPrec nmap (_, Prec n n') o =
  (nMapLookup n nmap, nMapLookup n' nmap) : o
mkPrec _ _ o = o

mkNon :: (Pos, AForm) -> [Term] -> [Term]
mkNon (_, Non t) ts = t : ts
mkNon _ ts = ts

mkPnon :: (Pos, AForm) -> [Term] -> [Term]
mkPnon (_, Pnon t) ts = t : ts
mkPnon _ ts = ts

mkUniq :: (Pos, AForm) -> [Term] -> [Term]
mkUniq (_, Uniq t) ts = t : ts
mkUniq (_, UniqAt t _) ts = t : ts
mkUniq _ ts = ts

mkConf :: (Pos, AForm) -> [Term] -> [Term]
mkConf (_, Conf t) ts = t : ts
mkConf _ ts = ts

mkAuth :: (Pos, AForm) -> [Term] -> [Term]
mkAuth (_, Auth t) ts = t : ts
mkAuth _ ts = ts

mkFact :: [(Term, Sid)] -> (Pos, AForm) -> [Fact] -> [Fact]
mkFact nmap (_, AFact name fs) ts =
  Fact name (map f fs) : ts
  where
    f t =
      case lookup t nmap of
        Just s -> FSid s
        Nothing -> FTerm t
mkFact _ _ ts = ts

checkUniqAt :: MonadFail m => [(Term, Sid)] -> Preskel -> (Pos, AForm) -> m ()
checkUniqAt nmap k (pos, UniqAt t n) =
  case lookup t $ korig k of
    Nothing -> fail (shows pos "Atom not unique at node")
    Just ns
      | elem (nMapLookup n nmap) ns -> return ()
      | otherwise -> fail (shows pos "Atom not unique at node")
checkUniqAt _ _ _ = return ()
