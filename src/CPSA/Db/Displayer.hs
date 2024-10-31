-- Summarize CPSA output as a formula in coherent logic

-- Copyright (c) 2011 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Db.Displayer (display) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Entry (writeSExpr)
import CPSA.Algebra
import CPSA.Protocol (Trace)
import CPSA.Db.Loader (strip, massoc, loadStrandMap)
import CPSA.Db.Structs
import CPSA.Db.Tree

import Text.Printf (printf)

-- Print forest
display :: Handle -> Int -> Forest -> IO ()
display h m f = mapM_ (writeSExpr h m) (concatMap rootFacts f)

rootFacts :: Tree -> [SExpr ()]
rootFacts t = L () [S () "root", S () (displaySkel $ label $ vertex t)] :
    treeFacts t

treeFacts :: Tree -> [SExpr ()]
treeFacts t = skeletonFacts (vertex t)
    ++ concatMap treeFacts (children t)
    ++ concatMap (stepFacts (vertex t) . vertex) (children t)

skeletonFacts :: Skel -> [SExpr ()]
skeletonFacts s = L () [S () "skeleton", S () (displaySkel $ label s)] : []
                    -- TODO: add remaining skeleton facts


-- traceFacts :: Trace -> [SExpr ()]

stepFacts :: Skel -> Skel -> [SExpr ()]
stepFacts from to = let stepSym = S () (displayStep (label from) (label to)) in
                    L () [S () "step", S () (displaySkel $ label from),
                            stepSym,
                            S () (displaySkel $ label to)] :
                    case massoc "operation" (alist to) of
                        Just (op:_) -> [L () [strip op, stepSym]] -- TODO: match on op and use specific arg data
                        _ -> []


displaySkel :: Int -> String
displaySkel = printf "skel_%d"

-- displayStrand :: Int -> Int -> String
-- displayStrand = printf "strand_%d_%d"

displayStep :: Int -> Int -> String
displayStep = printf "step_%d_%d"
