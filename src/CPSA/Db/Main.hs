-- Prints the output of a CPSA run as a Prolog database.

-- This programs loads CPSA output.  It assembles the skeletons in the
-- output into a forest of derivation trees.  It then prints the
-- forest in Prolog syntax.  To be loadable by Prolog, the output must
-- be sorted so that clauses of one predicate are colocated.

-- The output should be used by SWI Prolog as strings must not be atoms.
-- Load the generated file using consult/1.

-- Copyright (c) 2024 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Lib.Printer
import CPSA.Db.Loader
import CPSA.Db.Tree

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      ks <- loadPreskels p
      h <- outputHandle output
      writeComment h margin cpsaVersion
      writeComment h margin "Database"
      db h (pp margin defaultIndent) (forest ks)
      hClose h

-- Load preskeletons
loadPreskels :: PosHandle -> IO ([Preskel])
loadPreskels h =
    do
      (_, k, s) <- loadFirst h
      ks <- loop [k] s
      return ks
    where
      loop ks s =
          do
            n <- loadNext s
            case n of
              Nothing ->        -- EOF
                  return $ reverse ks
              Just (k, s) ->
                  loop (k:ks) s

writeCpsaLn :: Handle -> (SExpr a -> String) -> SExpr a -> IO ()
writeCpsaLn h printer sexpr =
    hPutStrLn h $ printer sexpr

-- Print forest
db :: Handle -> (SExpr () -> String) -> Forest -> IO ()
db h printer f =
    mapM_ (root h printer) f

root :: Handle -> (SExpr () -> String) -> Tree -> IO ()
root h printer t =
    do
      hPutStrLn h ""
      writeCpsaLn h printer (L () [S () "root", N () (label $ vertex t)])
      tree h printer t

tree :: Handle -> (SExpr () -> String) -> Tree -> IO ()
tree h printer t =
    do
      let l = label $ vertex t
      body h printer l (alist $ vertex t)
      strands h printer l 0 (alist $ vertex t)
      mapM_ (child h printer l) (children t)
      mapM_ (dup h printer l) (seen $ vertex t)

body :: Handle  -> (SExpr () -> String) -> Int -> [SExpr Pos] -> IO ()
body h printer l xs =
    writeCpsaLn h printer (L () (S () "skel" : N () l : map strip xs))

strands :: Handle -> (SExpr () -> String) -> Int -> Int -> [SExpr Pos] -> IO ()
strands _ _ _ _ [] =
    return ()
strands h printer l s (x@(L _ (S _ "defstrand" : _)) : xs) =
    do
      let y = L () [S () "strand", N () l, N () s, strip x]
      writeCpsaLn h printer y
      strands h printer l (s + 1) xs
strands h printer l s (x@(L _ (S _ "deflistener" : _)) : xs) =
    do
      let y = L () [S () "strand", N () l, N () s, strip x]
      writeCpsaLn h printer y
      strands h printer l (s + 1) xs
strands h printer l s (_ : xs) =
    strands h printer l s xs

child :: Handle -> (SExpr () -> String) -> Int -> Tree -> IO ()
child h printer l t =
    do
      let lab = label $ vertex t
      writeCpsaLn h printer (L () [S () "child", N () l, N () lab])
      case assoc "operation" (alist $ vertex t) of
        Just op ->
            do
              let x = L () [S () "step",
                            N () l,
                            L () (S () "operation" : map strip op),
                            N () lab]
              writeCpsaLn h printer x
              tree h printer t
        _ ->
            do
              writeCpsaLn h printer (L () [N () l, L () [], N () l])
              tree h printer t

dup :: Handle -> (SExpr () -> String) -> Int -> (Int, SExpr Pos) -> IO ()
dup _ _ l (lab, _) | l == lab = return () -- Ignore self loops
dup h printer l (lab, op) =
    do
      let x = L () [S () "step",
                    N () l,
                    strip op,
                    N () lab]
      writeCpsaLn h printer x
