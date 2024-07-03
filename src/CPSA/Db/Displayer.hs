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

-- Print forest
display :: Handle -> Int -> Forest -> IO ()
display h m f = mapM_ (root h m) f

root :: Handle -> Int -> Tree -> IO ()
root h m t =
    do
      hPutStrLn h ""
      let x = L () [S () "root", N () (label $ vertex t)]
      writeSExpr h m x
      tree h m t t

tree :: Handle -> Int -> Tree -> Tree -> IO ()
tree h m r t =
    do
      let skel = vertex t
      let l = label skel
      body h m l (alist skel)
      mapM_ (displayTrace h m skel) (zip [0..] (ktraces skel))
      mapM_ (child h m r skel) (children t)
      mapM_ (dup h m r skel) (seen $ vertex t)

body :: Handle -> Int -> Int -> [SExpr Pos] -> IO ()
body h m l xs =
    do
      let alist = map strip xs
      let x = L () [S () "skel", N () l, L () alist]
      writeSExpr h m x
      displayVals h m "uniq" l (massoc "uniq-orig" alist)
      displayVals h m "ugen" l (massoc "uniq-gen" alist)
      displayVals h m "non" l (massoc "non-orig" alist)
      displayVals h m "pnon" l (massoc "pen-non-orig" alist)
      displayVals h m "conf" l (massoc "conf" alist)
      displayVals h m "auth" l (massoc "conf" alist)
      displayItems h m "prec" l (massoc "precedes" alist)
      displayItems h m "leads-to" l (massoc "leads-to" alist)
      displayItems h m "fact" l (massoc "facts" alist)
      
displayVals :: Handle -> Int -> String -> Int -> Maybe [SExpr ()] -> IO ()
displayVals _ _ _ _ Nothing = return ()
displayVals h m key l (Just vals) =
    do
      let x = L () (S () key : N () l : vals)
      writeSExpr h m x

displayItems :: Handle -> Int -> String -> Int -> Maybe [SExpr ()] -> IO ()
displayItems _ _ _ _ Nothing = return ()
displayItems h m key l (Just facts) =
    mapM_ f facts
    where
      f (L () fact) =
          do
            let x = L () (S () key : N () l : fact)
            writeSExpr h m x
      f x = fail (shows (annotation x) "Malformed item")
                 
displayTrace :: Handle -> Int -> Skel -> (Int, Trace) -> IO ()
displayTrace h m k strace =
      mapM_ (displayRoleMatch h m k strace) (roles $ prot k)

displayRoleMatch :: Handle -> Int -> Skel -> (Int, Trace) -> Role -> IO ()
displayRoleMatch h m k (s, trace) role =
    case matchTraces (rtrace role) trace (kgen k, emptyEnv) of
      [] -> return ()
      (_, e) : _->
          do
            let l = label k
            let len = length trace
            let x = L () [S () "l", N () l, Q () (rname role),
                          N () s, N () len]
            writeSExpr h m x
            mapM_ (displayParam h m l role s)
                    (displayEnv (rctx role) (kctx k) e)

displayParam :: Handle -> Int -> Int -> Role -> Int -> SExpr () -> IO ()
displayParam h m l role s (L () [S () param, val]) =
    do
      let x = L () [S () "p", N () l, Q () (rname role),
                    Q () param, N () s, val]
      writeSExpr h m x
displayParam _ _ _ role _ _ =
    fail ("Bad parameter in role " ++ rname role)

child :: Handle -> Int -> Tree -> Skel -> Tree -> IO ()
child h m r k t =
    do
      let l = label k
      let lab = label $ vertex t
      let x = L () [S () "child", N () l, N () lab]
      writeSExpr h m x
      case massoc "operation" (alist $ vertex t) of
        Just op ->
            do
              let y = L () [S () "step", N () l,
                            L () (map strip op),
                            N () lab]
              writeSExpr h m y
              case massoc "strand-map" (alist $ vertex t) of
                Just xs@(_ : _) ->
                    do
                      mapping <- mapM loadStrandMap xs
                      twa h m k (vertex t) (map strip op) mapping
                _ -> return ()
              tree h m r t
        _ ->
            do
              let y = L () [S () "step", N () l, L () [], N () lab]
              writeSExpr h m y
              tree h m r t

dup :: Handle -> Int -> Tree -> Skel -> (Int, [SExpr a], [Int]) -> IO ()
dup _ _ _ k (lab, _, _) | label k == lab = return () -- Ignore self loops
dup h m r k (lab, op, mapping) =
    do
      let l = label k
      let dop = map strip op
      let x = L () [S () "step", N () l, L () dop, N () lab]
      writeSExpr h m x
      case findSkel lab r of
        Nothing ->
            hPutStrLn h ("; Cannot find " ++ show lab)
        Just k' ->
            do
              hPutStrLn h ("; Seen child " ++ show l ++
                           " -> " ++ show (label k'))
              twa h m k k' dop mapping

twa :: Handle -> Int -> Skel -> Skel -> [SExpr ()] -> [Int] -> IO ()
twa h m k k' op@(S () "generalization" : _) mapping =
    rtwa h m k k' (L () op) mapping
twa h m k k' op mapping =
    ftwa h m k k' (L () op) mapping

ftwa :: Handle -> Int -> Skel -> Skel -> SExpr () -> [Int] -> IO ()
ftwa h m k k' op mapping =
    case mtwa k k' mapping of
      Nothing -> hPutStrLn h "; No forward mapping"
      Just env ->
          do
            let l = label k
            let l' = label k'
            mapM_ (strands h m l l' op) (zip [0..] mapping)
            mapM_ (bindings h m l l' op) env

rtwa :: Handle -> Int -> Skel -> Skel -> SExpr () -> [Int] -> IO ()
rtwa h m k k' op mapping =
    case mtwa k' k mapping of
      Nothing -> hPutStrLn h "; No reverse mapping"
      Just env ->
          do
            let l = label k
            let l' = label k'
            mapM_ (strands h m l l' op) (zip mapping [0..])
            mapM_ (bindings h m l l' op) (map swap env)
    where
      swap (x, y) = (y, x)

strands :: Handle -> Int -> Int -> Int -> SExpr () -> (Int, Int) -> IO ()
strands h m l l' op (s, s') =
    do
      let x = L () [S () "stwa", N () l, N () s, op,
                    N () l', N () s']
      writeSExpr h m x

bindings :: Handle -> Int -> Int -> Int -> SExpr () ->
            (SExpr (), SExpr ()) -> IO ()
bindings h m l l' op (t, t') =
    do
      let x = L () [S () "mtwa", N () l, t, op, N () l', t']
      writeSExpr h m x
