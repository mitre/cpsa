-- Prints the output of a CPSA run as a Prolog database.

-- This programs loads CPSA output.  It assembles the skeletons in the
-- output into a forest of derivation trees.  It then prints the
-- forest in Prolog syntax.  To be loadable by Prolog, the output must
-- be sorted so that clauses of one predicate are colocated.

-- The output should be used SWI Prolog as strings must not be atoms.
-- Load the generated file using consult/1.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import Text.Printf (printf)
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Prolog.Loader
import CPSA.Prolog.Tree

main :: IO ()
main =
    do
      (p, (output, _)) <- start filterOptions filterInterp
      ks <- loadPreskels p
      h <- outputHandle output
      prolog h (forest ks)
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

-- Print forest
prolog :: Handle -> Forest -> IO ()
prolog h f = mapM_ (root h) f

root :: Handle -> Tree -> IO ()
root h t =
    do
      hPutStrLn h (printf "root(%d)." (label $ vertex t))
      tree h t

tree :: Handle -> Tree -> IO ()
tree h t =
    do
      let l = label $ vertex t
      body h l (alist $ vertex t)
      mapM_ (child h l) (children t)
      mapM_ (cohort h l) (children t ++ duplicates t)

body :: Handle -> Int -> [SExpr Pos] -> IO ()
body h l xs =
    do
      hPutStr h (printf "skel(%d, " l)
      sexprs h xs
      hPutStrLn h ")."

sexprs :: Handle -> [SExpr Pos] -> IO ()
sexprs h [] =
    hPutStr h "[]"
sexprs h (x : xs) =
    do
      hPutStr h "["
      sexpr h x
      rest h xs
      hPutStr h "]"

sexpr :: Handle -> SExpr Pos -> IO ()
sexpr h (S _ s) =
    hPutStr h s
sexpr h (Q _ q) =
    do
      hPutStr h "\""
      hPutStr h q
      hPutStr h "\""
sexpr h (N _ n) =
    hPutStr h (printf "%d" n)
sexpr h (L _ xs) =
    sexprs h xs

rest :: Handle -> [SExpr Pos] -> IO ()
rest _ [] =
    return ()
rest h (x : xs) =
    do
      hPutStr h ", "
      sexpr h x
      rest h xs

child :: Handle -> Int -> Tree -> IO ()
child h l t =
    do
      hPutStrLn h (printf "child(%d, %d)." l (label $ vertex t))
      tree h t

cohort :: Handle -> Int -> Tree -> IO ()
cohort h l t =
    hPutStrLn h (printf "cohort(%d, %d)." l (label $ vertex t))
