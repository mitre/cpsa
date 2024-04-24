module CPSA.Db.Structs (Prot (..), Role (..), Skel (..)) where

import CPSA.Algebra
import CPSA.Signature (Sig)
import CPSA.Protocol (Trace)
import CPSA.Lib.SExpr

data Role = Role
    { rname :: String,  -- Role name
      rvars :: ![Term], -- Set of role variables
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
      ktraces :: [Trace], --Strands
      label :: Int,             -- Label from the input or generated
                                -- by the loader
      parent :: Maybe Int,      -- Parent from the input
      -- Seen preskeletons isomorphic to cohort members
      -- with their operation field
      seen :: [(Int, SExpr Pos)],
      alist :: [SExpr Pos] }
    deriving Show
