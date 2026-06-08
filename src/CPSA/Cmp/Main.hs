-- Compare the SHAPE SETS of two CPSA output files up to pov-respecting
-- isomorphism, PER PROBLEM, reporting the witnessing shape pairing.
--
-- EXPERIMENT (global shape subsumption) validation tool.
--
-- cpsa4diff compares two runs S-expression by S-expression and stops at
-- the first textual difference.  That is useless for validating the
-- global-shapes experiment, because the flag-ON derivation tree
-- deliberately differs from stock.  What we want to know is whether the
-- *set of shapes* is the same.
--
-- This tool loads the shape skeletons from each file (every defskeleton
-- carrying a (shape) marker, with its defprotocol) into real Preskels via
-- the standard Loader, then checks, WITHIN EACH PROBLEM, that the two
-- shape collections are equal as multisets under POINT-OF-VIEW-respecting
-- skeleton isomorphism (probIsomorphicWith): two shapes are "the same"
-- only if isomorphic via a strand permutation that respects their
-- pov->strand maps.  A protocol can have shapes that are bare-isomorphic
-- yet pov-distinct; those must NOT be merged.  The pov maps are recovered
-- from each shape's (maps ...) field, which the loader ignores.
--
-- Work is done PER PROBLEM (like cpsa4subsume): each file is split at its
-- defprotocol boundaries (cpsa4 reprints the protocol once per problem),
-- and problem i of the first file is compared against problem i of the
-- second.  We ASSUME the two files analyze the same problems in the same
-- order; if the problem counts differ, or a matched pair's protocol names
-- differ, the tool fails loudly rather than silently skipping.
--
-- For each problem the tool prints the witnessing pairing: every
-- "iso: L_i <-> L_j" match (by skeleton label) and any shape left
-- unmatched on either side.  Because probIsomorphicWith is symmetric, a
-- single direction per candidate pair suffices.  Exit status is 0 iff
-- every problem matches one-for-one.

module Main (main) where

import System.IO
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import CPSA.Lib.SExpr (SExpr (..), Pos, posHandle)
import CPSA.Lib.Expand (readSExprs)
import CPSA.Algebra (origin)
import CPSA.Signature (defaultSig)
import CPSA.Loader (loadSExprs)
import CPSA.Strand (Preskel, nstrands, probIsomorphicWith)

-- A shape: its skeleton label (if any), its Preskel, and its pov->strand
-- map (prob, parsed from (maps)).
data Shape = Shape
    { shapeLabel :: Maybe Int
    , shapeK     :: Preskel
    , shapeProb  :: [Int] }

-- A problem: the protocol name it analyzes and its shapes.
data Problem = Problem String [Shape]

main :: IO ()
main =
    do
      args <- getArgs
      case args of
        [f1, f2] ->
            do
              ps1 <- loadProblems f1
              ps2 <- loadProblems f2
              ok <- compareRuns f1 f2 ps1 ps2
              if ok then exitSuccess else exitFailure
        _ ->
            do
              hPutStrLn stderr "usage: cpsa4cmp FILE1 FILE2"
              exitFailure

-- Load a file's problems.  Drop any leading material before the first
-- defprotocol, then split into per-problem chunks and load each.
loadProblems :: String -> IO [Problem]
loadProblems fn =
    do
      h <- openFile fn ReadMode
      ph <- posHandle fn h
      sexprs <- readSExprs ph
      mapM loadProblem (groupProblems (dropWhile (not . isDefprotocol) sexprs))

-- Load one problem chunk (defprotocol followed by its defskeletons).
-- loadSExprs reconstructs each shape defskeleton into a Preskel; we zip
-- those with the label and prob recovered from the S-expressions.
loadProblem :: [SExpr Pos] -> IO Problem
loadProblem chunk =
    do
      let dp = head chunk                    -- the defprotocol
          shapeSExprs = filter isShapeDefskel chunk
      ks <- loadSExprs defaultSig (algOf dp) origin (dp : shapeSExprs)
      let shapes = [ Shape (labelOf s) k (probOf s k)
                   | (s, k) <- zip shapeSExprs ks ]
      return (Problem (nameOf dp) shapes)

-- Compare two runs problem by problem.  Fail loudly if the problem
-- counts differ; otherwise compare matched pairs in order.
compareRuns :: String -> String -> [Problem] -> [Problem] -> IO Bool
compareRuns f1 f2 ps1 ps2
    | length ps1 /= length ps2 =
        do
          putStrLn (f1 ++ ": " ++ show (length ps1) ++ " problems; " ++
                    f2 ++ ": " ++ show (length ps2) ++
                    " problems; PROBLEM SETS DIFFER")
          return False
    | otherwise =
        do
          results <- mapM (\(i, a, b) -> comparePair i a b)
                          (zip3 [1 :: Int ..] ps1 ps2)
          let ok = and results
          putStrLn ("OVERALL: " ++
                    (if ok then "ISOMORPHIC shape sets"
                           else "MISMATCH"))
          return ok

-- Compare one problem's shapes.  Print the witnessing pairing and the
-- leftovers; the pair matches iff nothing is left over (and the protocol
-- names agree).
comparePair :: Int -> Problem -> Problem -> IO Bool
comparePair i (Problem nm1 ss1) (Problem nm2 ss2) =
    do
      putStrLn ("Problem " ++ show i ++ " (" ++ nm1 ++ "): " ++
                show (length ss1) ++ " vs " ++ show (length ss2) ++ " shapes")
      mapM_ (\(a, b) -> putStrLn ("  iso: " ++ lbl a ++ " <-> " ++ lbl b)) pairs
      mapM_ (\a -> putStrLn ("  only in first:  " ++ lbl a)) only1
      mapM_ (\b -> putStrLn ("  only in second: " ++ lbl b)) only2
      if not nameOk
        then putStrLn ("  PROTOCOL NAME MISMATCH: " ++ nm1 ++ " vs " ++ nm2)
        else return ()
      let ok = null only1 && null only2 && nameOk
      putStrLn ("  => " ++ (if ok then "ISOMORPHIC" else "MISMATCH"))
      return ok
    where
      (pairs, only1, only2) = matchShapes ss1 ss2
      nameOk = nm1 == nm2
      lbl s = maybe "?" show (shapeLabel s)

-- Greedy one-to-one matching of two shape lists under pov-respecting
-- isomorphism.  Returns the matched pairs and the unmatched remainders
-- of each side.
matchShapes :: [Shape] -> [Shape] -> ([(Shape, Shape)], [Shape], [Shape])
matchShapes [] bs = ([], [], bs)
matchShapes (a : as) bs =
    case extract a bs of
      Nothing ->
          let (ps, o1, o2) = matchShapes as bs in (ps, a : o1, o2)
      Just (b, bs') ->
          let (ps, o1, o2) = matchShapes as bs' in ((a, b) : ps, o1, o2)

-- Remove the first shape isomorphic to a, returning it and the rest.
extract :: Shape -> [Shape] -> Maybe (Shape, [Shape])
extract _ [] = Nothing
extract a (b : bs)
    | iso a b   = Just (b, bs)
    | otherwise = fmap (\(x, xs) -> (x, b : xs)) (extract a bs)

-- Pov-respecting isomorphism.  Equal-length pov maps are required
-- (probIsomorphicWith indexes by pov strand); within one problem all
-- shapes share the pov so this always holds, but the guard keeps the
-- tool safe if mismatched shapes are ever compared.
iso :: Shape -> Shape -> Bool
iso a b =
    length (shapeProb a) == length (shapeProb b) &&
    probIsomorphicWith (shapeProb a) (shapeProb b) (shapeK a) (shapeK b)

-- Recognizers and field extractors (shared with cpsa4subsume) ---------

isDefprotocol :: SExpr a -> Bool
isDefprotocol (L _ (S _ "defprotocol" : _)) = True
isDefprotocol _ = False

-- Split a list that starts with a defprotocol into per-problem chunks,
-- each beginning at a defprotocol and running to just before the next.
groupProblems :: [SExpr Pos] -> [[SExpr Pos]]
groupProblems [] = []
groupProblems (dp : xs) =
    let (body, rest) = break isDefprotocol xs
    in (dp : body) : groupProblems rest

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

-- The protocol name a defprotocol declares.
nameOf :: SExpr a -> String
nameOf (L _ (S _ "defprotocol" : S _ nm : _)) = nm
nameOf _ = "?"

-- The (label N) of a defskeleton.
labelOf :: SExpr a -> Maybe Int
labelOf (L _ (_ : rest)) =
    case [ n | L _ [S _ "label", N _ n] <- rest ] of
      (n : _) -> Just n
      []      -> Nothing
labelOf _ = Nothing

-- The pov->strand map (prob) from a shape's (maps ...) field.  Every map
-- entry carries the same strand list, so the first entry suffices.  An
-- empty/absent (maps) means the skeleton is the pov; prob is the identity.
probOf :: SExpr a -> Preskel -> [Int]
probOf (L _ (_ : rest)) k =
    case [ entries | L _ (S _ "maps" : entries) <- rest ] of
      (L _ (L _ strands : _) : _) : _ -> [ n | N _ n <- strands ]
      _ -> [0 .. nstrands k - 1]
probOf _ k = [0 .. nstrands k - 1]
