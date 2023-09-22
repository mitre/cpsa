-- Loads preskeletons and returns the results for display.  An error
-- is signaled if the ordering relation is cyclic.  For preskeleton
-- input without labels, a unique label is added.  The representation
-- of each strand includes its trace, but not its environment.
-- Ordering relations implied by transitive closure are eliminated so
-- as to reduce clutter.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Query.Loader (Preskel, label, parent, seen, alist, strip,
                          assoc, nassoc, State, loadFirst, loadNext)
                          where

import qualified Data.List as L
import CPSA.Lib.SExpr
import CPSA.Lib.Entry (gentlyReadSExpr)

-- A view of preskeletons designed for queries.

data Preskel = Preskel
    { label :: Int,             -- Label from the input or generated
                                -- by the loader
      parent :: Maybe Int,      -- Parent from the input
      seen :: [Int], -- Seen preskeletons isomorphic to cohort members
      alist :: [SExpr ()] }     -- Body of this preskeleton
    deriving Show

instance Eq Preskel where
    k0 == k1 = label k0 == label k1

instance Ord Preskel where
    compare k0 k1 = compare (label k0) (label k1)

-- The remaing is in support of the loader

-- Load one preskeleton at a time from the input.  The state of
-- loading follows.

newtype State = State (PosHandle, Int)

-- Load the initial comments and the first preskeleton.  It's an error
-- if there is no preskeleton in the input.

loadFirst :: PosHandle -> IO ([SExpr Pos], Preskel, State)
loadFirst h =
    loadComments h []

loadComments :: PosHandle -> [SExpr Pos]
             -> IO ([SExpr Pos], Preskel, State)
loadComments h cmts =
    do
      x <- gentlyReadSExpr h
      case x of
        Nothing -> fail "Empty input"
        Just x ->
            case x of
              cmt@(L _ (S _ "comment" : _)) ->
                  loadComments h (cmt:cmts)
              cmt@(L _ (S _ "herald" : _)) ->
                  loadComments h (cmt:cmts)
              _ ->
                  do
                    n <- loadSExpr (State (h, 0)) x
                    case n of
                      Nothing -> fail "Empty input"
                      Just (p, s) -> return (reverse cmts, p, s)

-- Load the next preskeleton or return Nothing on EOF
loadNext :: State -> IO (Maybe (Preskel, State))
loadNext s@(State (h, _)) =
    do
      x <- gentlyReadSExpr h
      case x of
        Nothing -> return Nothing
        Just x -> loadSExpr s x

-- Load from one S-expression
loadSExpr :: State -> SExpr Pos -> IO (Maybe (Preskel, State))
loadSExpr (State (h, tag)) x@(L pos (S _ "defskeleton" : xs)) =
    do
      k <- loadPreskel x pos tag xs
      return (Just (k, State (h, 1 + max tag (label k))))
loadSExpr s (L _ (S _ "defprotocol" : _)) =
    loadNext s
loadSExpr s (L _ (S _ "comment" : _)) =
    loadNext s
loadSExpr _ x = fail (shows (annotation x) "Malformed input")

-- Preskeletons

loadPreskel :: MonadFail m => SExpr Pos -> Pos ->
               Int -> [SExpr Pos] -> m Preskel
loadPreskel _ _ tag (S _ _ : (L _ (S _ "vars" : _)) : xs) =
    do
      checkAlist xs -- Ensure alist syntax
      label <- nassoc "label" xs
      parent <- nassoc "parent" xs
      seen <- nsassoc "seen" xs
      return Preskel { label = maybe tag id label,
                       parent  = parent,
                       seen = maybe [] (L.sort . L.nub) seen,
                       alist = map strip xs }
loadPreskel _ pos _ _ = fail (shows pos "Malformed skeleton")

-- Strip positions from an S-expression

strip :: SExpr a -> SExpr ()
strip (S _ s) = S () s
strip (Q _ s) = Q () s
strip (N _ n) = N () n
strip (L _ l) = L () (map strip l)

-- Ensure alist has the proper form
checkAlist :: MonadFail m => [SExpr Pos] -> m ()
checkAlist [] = return ()
checkAlist ((L _ (S _ _ : _)) : xs) = checkAlist xs
checkAlist xs = fail (shows (annotation $ head xs) "Malformed association list")

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr Pos] -> Maybe [SExpr Pos]
assoc key alist =
    loop alist Nothing
    where
      loop ((L _ (S _ head : tail)) : rest) vals
          | key == head = loop rest (extend tail vals)
          | otherwise = loop rest vals
      loop _ vals = vals
      extend x Nothing = Just x
      extend x (Just y) = Just (x ++ y)

-- assoc key alist =
--    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]

nassoc :: MonadFail m => String -> [SExpr Pos] -> m (Maybe Int)
nassoc key xs =
    case assoc key xs of
      Nothing -> return Nothing
      Just [val] ->
          do
            ns <- num val
            return (Just ns)
      Just (x:_) -> fail (shows (annotation x) "Expecting one number")
      Just [] -> fail (shows (annotation (head xs)) "Expecting one number")

num :: MonadFail m => SExpr Pos -> m Int
num (N _ n) = return n
num x = fail (shows (annotation x) "Expecting a number")

nsassoc :: MonadFail m => String -> [SExpr Pos] -> m (Maybe [Int])
nsassoc key xs =
    case assoc key xs of
      Nothing -> return Nothing
      Just val ->
          do
            ns <- mapM num val
            return (Just ns)
