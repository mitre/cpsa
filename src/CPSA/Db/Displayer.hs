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
skeletonFacts s =   L () [S () "skel", S () (displaySkel $ label s)] :
                    strandFacts s ++
                    termProps s "uniq" "uniq-orig" ++
                    termProps s "ugen" "uniq-gen" ++
                    termProps s "non" "non-orig" ++
                    termProps s "pnon" "pen-non-orig" ++
                    channelProps s "auth" ++
                    channelProps s "conf" ++
                    prec s ++
                    leadsto s ++
                    unrealized s ++
                    facts s ++
                    keyClauses "realized" s ++
                    keyClauses "shape" s ++
                    keyClauses "dead" s
                    -- TODO: add remaining skeleton facts

strandFacts :: Skel -> [SExpr ()]
strandFacts s = concat (zipWith fun (ktraces s) [0..])
    where 
        fun (role, env, trace) i = 
            let skelVar = S () (displaySkel (label s)) in
            let strandVar = S () (displayStrand (label s) i) in
                L () [S () "pl", skelVar, Q () role, strandVar, N () (length trace)]:
                map (\(k,v) -> L () [S () "p", skelVar, Q () role, strandVar, Q () k, v]) env
            


termProps :: Skel -> String -> String -> [SExpr ()]
termProps s k kl =
    case massoc kl (map strip (alist s)) of
    Just ts -> map f ts
        where f t = L () [S () k, S () (displaySkel $ label s), t]
    _ -> []

channelProps :: Skel -> String -> [SExpr ()]
channelProps s k =
    case massoc k (map strip (alist s)) of
    Just ts -> map f ts
        where f t = L () [S () k, S () (displaySkel $ label s), t]
    _ -> []

-- Returns nothing if the key is not present, and
-- a singleton if the key is present
keyClauses :: String -> Skel -> [SExpr ()]
keyClauses k s = case massoc k (map strip (alist s)) of
    Just _ -> [L () [S () k, S () (displaySkel $ label s)]]
    _ -> []

prec :: Skel -> [SExpr  ()]
prec s =
    case massoc "precedes" (map strip (alist s)) of
    Just l -> map f l
        where
            f (L () [L () [N () s1, N () i1], L () [N () s2, N () i2]]) =
                L () [S () "prec", S () (displaySkel $ label s), displayNode (label s) s1 i1, displayNode (label s) s2 i2]
            f _ = L () [S () "prec", S () "error"]
    _ -> []

leadsto :: Skel -> [SExpr  ()]
leadsto s =
    case massoc "leads-to" (map strip (alist s)) of
    Just l -> map f l
        where
            f (L () [L () [N () s1, N () i1], L () [N () s2, N () i2]]) =
                L () [S () "leads-to", S () (displaySkel $ label s), displayNode (label s) s1 i1, displayNode (label s) s2 i2]
            f _ = L () [S () "leads-to", S () "error"]
    _ -> []

unrealized :: Skel -> [SExpr ()]
unrealized s =
    case massoc "unrealized" (map strip (alist s)) of
    Just l -> map f l
        where
            f (L () [N () strand, N () index]) =
                L () [S () "unrealized", S () (displaySkel $ label s), displayNode (label s) strand index]
            f _ = L () [S () "unrealized"]
    _ -> []

facts :: Skel -> [SExpr ()]
facts s =
    case massoc "facts" (map strip (alist s)) of
    Just l -> map f l
        where
            f (L () (pred:args)) = L () (pred: S () (displaySkel $ label s): args)
            f _ = L () [S () "facts"]
    _ -> []



stepFacts :: Skel -> Skel -> [SExpr ()]
stepFacts from to = let stepSym = S () (displayStep (label from) (label to)) in
                    L () [S () "step", S () (displaySkel $ label from),
                            stepSym,
                            S () (displaySkel $ label to)] :
                    case massoc "operation" (alist to) of
                        Just (op:args) -> 
                            (case (strip op, map strip args) of
                                (S _ "generalization", typ:_) -> L () [S () "generalization", stepSym, typ]
                                (S _ "nonce-test", L _ (typ:_):_) -> L () [S () "nonce_test", stepSym, typ]
                                (S _ "encryption-test", L _ (typ:_):_) -> L () [S () "encryption_test", stepSym, typ]
                                (S _ "channel-test", L _ (typ:_):_) -> L () [S () "channel_test", stepSym, typ]
                                (s, args) -> L () (s:args)) :
                            case strip op of
                                S _ "generalization" -> rtwa from to
                                _ -> ftwa from to
                        _ -> []



ftwa :: Skel -> Skel -> [SExpr ()]
ftwa k k' = case massoc "strand-map" (map strip (alist k')) of
    Just mapping -> zipWith fun [0..] mapping
        where
            fun f (N () t) = L () [S () "stwa", S () (displayStrand (label k) f), S () (displayStep (label k) (label k')), S () (displayStrand (label k') t) ]
            fun _ _ = Q () "non-number in strand-map"
    _ -> []

rtwa :: Skel -> Skel -> [SExpr ()]
rtwa k k' = case massoc "strand-map" (map strip (alist k')) of
    Just mapping -> zipWith fun mapping [0..]
        where
            fun (N () f) t = L () [S () "stwa", S () (displayStrand (label k) f), S () (displayStep (label k) (label k')), S () (displayStrand (label k') t) ]
            fun _ _ = Q () "non-number in strand-map"
    _ -> []












displaySkel :: Int -> String
displaySkel = printf "skel_%d"

displayStep :: Int -> Int -> String
displayStep = printf "step_%d_%d"

displayStrand :: Int -> Int -> String
displayStrand = printf "strand_%d_%d"

displayNode :: Int -> Int -> Int -> SExpr ()
displayNode skel strand index =
    L () [S () "node", S () (displayStrand skel strand), N () index]
