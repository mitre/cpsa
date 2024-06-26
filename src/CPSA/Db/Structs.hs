module CPSA.Db.Structs (Prot (..), Role (..), Skel (..),
                        matchTraces, mtwa) where

import Control.Monad
import qualified Data.List as L
import CPSA.Algebra
import CPSA.Signature (Sig)
import CPSA.Channel (cmMatch)
import CPSA.Protocol (Trace, Event (..))
import CPSA.Lib.SExpr

data Role = Role
    { rname :: String,  -- Role name
      rvars :: ![Term], -- Set of role variables
      rctx :: Context,
      rtrace :: !Trace } -- Events in causal order
    deriving Show

data Prot = Prot
    { pname :: String, -- Protocol name
      pgen :: Gen,     -- Generator for preskeletons
      roles :: [Role], -- Protocol roles including listener role
      psig :: Sig }    -- the protocol's signature
    deriving Show

data Skel = Skel
    { prot :: Prot,
      kvars :: [Term], -- Skeleton vars
      kctx :: Context,
      kgen :: Gen,
      ktraces :: [Trace], --Strands
      label :: Int,             -- Label from the input or generated
                                -- by the loader
      parent :: Maybe Int,      -- Parent from the input
      -- Seen preskeletons isomorphic to cohort members
      -- with their operation field
      seen :: [(Int, [SExpr Pos], [Int])],
      alist :: [SExpr Pos] }
    deriving Show

homomorphism :: Skel -> Skel -> [Int] -> [Env]
homomorphism k k' mapping =
    if L.length mapping == L.length (ktraces k)
    then
        let gg = gmerge (kgen k) (kgen k') in
        let strandids = take (L.length (ktraces k)) [0..] in
        let ge = foldM (matchStrand k k' mapping) (gg, emptyEnv) strandids in
        map snd ge
    else []

matchStrand :: Skel -> Skel -> [Int] -> (Gen, Env) -> Int -> [(Gen, Env)]
matchStrand k k' mapping env s =
    matchTraces (ktraces k !! s) (ktraces k' !! s') env
    where
      s' = mapping !! s

matchTraces :: Trace -> Trace -> (Gen, Env) -> [(Gen, Env)]
matchTraces _ [] env = [env]    -- Target can be shorter
matchTraces (In t : c) (In t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces (Out t : c) (Out t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces _ _ _ = []

mtwa :: Skel -> Skel -> [Int] -> Maybe [(SExpr (), SExpr ())]
mtwa k k' mapping =
    case homomorphism k k' mapping of
      [] -> Nothing
      env : _ ->
          Just (map (displayMaplet (kctx k) (kctx k')) maplets)
          where
            maplets = reify (kvars k) env

displayMaplet :: Context -> Context -> (Term, Term) ->
                 (SExpr (), SExpr ())
displayMaplet domain range (x, t)=
    (displayTerm domain x, displayTerm range t)
