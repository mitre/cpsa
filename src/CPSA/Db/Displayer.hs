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
import CPSA.Channel
import CPSA.Protocol (Event (..), Trace)
import CPSA.Db.Loader (strip, massoc)
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
      tree h m t

tree :: Handle -> Int -> Tree -> IO ()
tree h m t =
    do
      let skel = vertex t
      let l = label skel
      body h m l (alist skel)
      mapM_ (displayTrace h m skel) (zip [0..] (ktraces skel))
      mapM_ (child h m l) (children t)
      mapM_ (dup h m l) (seen $ vertex t)

body :: Handle -> Int -> Int -> [SExpr Pos] -> IO ()
body h m l xs =
    do
      let x = L () [S () "skel", N () l, L () (map strip xs)]
      writeSExpr h m x

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
            let x = L () [S () "p", N () l, Q () (rname role),
                          N () s, N () len]
            writeSExpr h m x
            mapM_ (displayParam h m l role s)
                    (displayEnv (rctx role) (kctx k) e)

matchTraces :: Trace -> Trace -> (Gen, Env) -> [(Gen, Env)]
matchTraces _ [] env = [env]    -- Target can be shorter than pattern
matchTraces (In t : c) (In t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces (Out t : c) (Out t' : c') env =
    do
      e <- cmMatch t t' env
      matchTraces c c' e
matchTraces _ _ _ = []

displayParam :: Handle -> Int -> Int -> Role -> Int -> SExpr () -> IO ()
displayParam h m l role s (L () [S () param, val]) =
    do
      let x = L () [S () "p", N () l, Q () (rname role),
                    N () s, Q () param, val]
      writeSExpr h m x
displayParam _ _ _ role _ _ =
    fail ("Bad parameter in role " ++ rname role)

{-
strands :: Handle -> Int -> Int -> [SExpr Pos] -> IO ()
strands _ _ _ [] =
    return ()
strands h l s (x@(L _ (S _ "defstrand" : _)) : xs) =
    do
      hPutStr h (printf "strand(%d, %d, " l s)
      sexpr h x
      hPutStrLn h ")."
      strands h l (s + 1) xs
strands h l s (x@(L _ (S _ "deflistener" : _)) : xs) =
    do
      hPutStr h (printf "strand(%d, %d, " l s)
      sexpr h x
      hPutStrLn h ")."
      strands h l (s + 1) xs
strands h l s (_ : xs) =
    do
      strands h l s xs

-}

child :: Handle -> Int -> Int -> Tree -> IO ()
child h m l t =
    do
      let lab = label $ vertex t
      let x = L () [S () "child", N () l, N () lab]
      writeSExpr h m x
      case massoc "operation" (alist $ vertex t) of
        Just op ->
            do
              let y = L () [S () "step", N () l,
                            L () (S () "operation" : map strip op),
                            N () lab]
              writeSExpr h m y
              tree h m t
        _ ->
            do
              let y = L () [S () "step", N () l, L () [], N () lab]
              writeSExpr h m y
              tree h m t

dup :: Handle -> Int -> Int -> (Int, SExpr a) -> IO ()
dup _ _ l (lab, _) | l == lab = return () -- Ignore self loops
dup h m l (lab, op) =
    do
      let x = L () [S () "step", N () l, strip op, N () lab]
      writeSExpr h m x
