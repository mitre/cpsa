-- Detect and relabel non-shape realized skeletons. 

-- Copyright (c) 2026, The MITRE Corporation
--
-- This program is free software: you cna redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.


-- When cpsa4 is run with generalization restricted to listener deletion
-- (the useGlobalShapes flag), every realized leaf is reported as a
-- (shape candidate). This filter reads such a run and repairs it.
-- Within each problem it determines, for every shape y, whether some
-- other shape x maps homomorphically onto it (respecting the point of
-- view). If so y is not really a shape; its (shape candidate) marker is 
-- rewritten to (seen x) (seen-ops (x (homomorphism-check m))), recording 
-- that the shape x subsumes y via the strand map m. Maximal shapes keep 
-- their (shape). Everything else in the file is passed through unchanged,
-- so the tree and all intermediate skeletons are preserved.
--
-- The pov->strand map (prob) needed for a pov-respecting homomorphism is
-- recovered from each shape's (maps ...) field (which the loader ignores);
-- the loader itself is unmodified.
--
-- Usage:  cpsa4 ... foo.scm | cpsa4subsume   (or cpsa4subsume foo.txt)

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Algebra (origin)
import CPSA.Signature (defaultSig)
import CPSA.Loader (loadSExprs)
import CPSA.Strand (Preskel, nstrands, homomorphismMapWith)

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      h <- outputHandle output
      writeComment h margin cpsaVersion
      writeComment h margin "Shapes patched by global shape check (cpsa4hom)"
      sexprs <- readAll p
      out <- processProblems sexprs
      mapM_ (writeLnSExpr h margin) out
      hClose h

-- Read every S-expression from the input.
readAll :: PosHandle -> IO [SExpr Pos]
readAll p =
    do
      x <- gentlyReadSExpr p
      case x of
        Nothing -> return []
        Just s -> do { rest <- readAll p; return (s : rest) }

-- The output is a sequence of problems, each introduced by a
-- (defprotocol ...) (cpsa4 prints the protocol once per problem). Split
-- on that boundary; any leading material before the first protocol is
-- passed through untouched.
processProblems :: [SExpr Pos] -> IO [SExpr ()]
processProblems sexprs =
    case break isDefprotocol sexprs of
      (leading, []) -> return (map strip leading)
      (leading, rest) ->
          do
            chunks <- mapM patchProblem (groupProblems rest)
            return (map strip leading ++ concat chunks)

-- Split a list that starts with a defprotocol into per-problem chunks,
-- each beginning at a defprotocol and running to just before the next.
groupProblems :: [SExpr Pos] -> [[SExpr Pos]]
groupProblems [] = []
groupProblems (dp : xs) =
    let (body, rest) = break isDefprotocol xs
    in (dp : body) : groupProblems rest

-- Patch one problem.  Load its shape skeletons, compute which are
-- covered, and rewrite their (shape) markers.  All other S-expressions
-- pass through unchanged.
patchProblem :: [SExpr Pos] -> IO [SExpr ()]
patchProblem chunk =
    case filter isShapeDefskel chunk of
      [] -> return (map strip chunk)   -- no shapes; nothing to do
      shapeSExprs ->
          do
            let dp = head chunk        -- the defprotocol
            preskels <- loadSExprs defaultSig (algOf dp) origin (dp : shapeSExprs)
            -- Per-shape record: (label, preskel, prob). prob comes from
            -- the (maps) field; an empty/absent maps means the shape is
            -- the pov itself, whose prob is the identity.
            let recs = [ (lbl, k, probOf s k)
                       | (s, k) <- zip shapeSExprs preskels
                       , Just lbl <- [labelOf s] ]
                verdict = homCheck recs
            return (map (emit verdict) chunk)

-- For each shape label, Nothing if it is a shape, or
-- Just (sourceLabel, strandMap) if a shape covers it.
homCheck :: [(Int, Preskel, [Int])] -> [(Int, Maybe (Int, [Int]))]
homCheck recs =
    [ (li, verdictFor li) | (li, _, _) <- recs ]
    where
      -- All homomorphism edges j -> i (j subsumes i) with witnessing map.
      edges = [ (lj, li, m)
              | (lj, kj, probj) <- recs, (li, ki, probi) <- recs, lj /= li
              , Just m <- [homomorphismMapWith probj probi kj ki] ]
      covered li = [ (lj, m) | (lj, li', m) <- edges, li' == li ]
      isShape li = null (covered li)
      verdictFor li =
          case covered li of
            [] -> Nothing
            ms -> case [ (lj, m) | (lj, m) <- ms, isShape lj ] of
                    (best : _) -> Just best   -- prefer a maximal (shape) subsumer
                    []         -> Just (head ms)

-- Emit one chunk element, rewriting a covered shape's marker.
emit :: [(Int, Maybe (Int, [Int]))] -> SExpr Pos -> SExpr ()
emit verdict s
    | isShapeDefskel s =
        case labelOf s >>= \lbl -> lookup lbl verdict of
          Just (Just (sl, m)) -> rewriteShape (strip s) sl m
          -- Surviving shape: promote a (shape candidate) marker to
          -- a plain (shape).
          _                   -> promoteShape (strip s)
    | otherwise = strip s

-- Normalize a surviving shape's (shape candidate) marker (from the
-- global shapes path) to a plain (shape).
promoteShape :: SExpr () -> SExpr ()
promoteShape (L () elems) = L () (map f elems)
    where f e | isShapeForm e = L () [S () "shape"]
              | otherwise = e
promoteShape s = s

-- Replace the (shape candidate) marker of a defskeleton with a seen/seen-ops pair
-- recording the subsuming shape sl and the homomorphism strand map m.
-- The skeleton keeps its (realized) marker and everything else.
rewriteShape :: SExpr () -> Int -> [Int] -> SExpr ()
rewriteShape (L () elems) sl m =
    L () (concatMap repl elems)
    where
      repl e | isShapeForm e =
                 [ L () [S () "seen", N () sl],
                   L () [S () "seen-ops",
                         L () [N () sl, L () (S () "homomorphism-check" : map (N ()) m)]] ]
             | otherwise = [e]
rewriteShape s _ _ = s

-- Recognizers and field extractors -----------------------------------

isDefprotocol :: SExpr a -> Bool
isDefprotocol (L _ (S _ "defprotocol" : _)) = True
isDefprotocol _ = False

isShapeDefskel :: SExpr a -> Bool
isShapeDefskel (L _ (S _ "defskeleton" : rest)) = any isShapeForm rest
isShapeDefskel _ = False

isShapeForm :: SExpr a -> Bool
isShapeForm (L _ (S _ "shape" : _)) = True
isShapeForm _ = False

-- The algebra name a defprotocol declares (default "basic").
algOf :: SExpr a -> String
algOf (L _ (S _ "defprotocol" : _ : S _ alg : _)) = alg
algOf _ = "basic"

-- The (label N) of a defskeleton.
labelOf :: SExpr a -> Maybe Int
labelOf (L _ (_ : rest)) =
    case [ n | L _ [S _ "label", N _ n] <- rest ] of
      (n : _) -> Just n
      []      -> Nothing
labelOf _ = Nothing

-- The pov->strand map (prob) from a shape's (maps ...) field. Every map
-- entry carries the same strand list, so the first entry suffices. An
-- empty (maps) means the skeleton is the pov; its prob is the identity.
probOf :: SExpr a -> Preskel -> [Int]
probOf (L _ (_ : rest)) k =
    case [ entries | L _ (S _ "maps" : entries) <- rest ] of
      (L _ (L _ strands : _) : _) : _ -> [ n | N _ n <- strands ]
      _ -> [0 .. nstrands k - 1]
probOf _ k = [0 .. nstrands k - 1]

-- Strip position annotations so new and old S-expressions share a type.
strip :: SExpr a -> SExpr ()
strip (S _ s)  = S () s
strip (Q _ s)  = Q () s
strip (N _ n)  = N () n
strip (L _ xs) = L () (map strip xs)
