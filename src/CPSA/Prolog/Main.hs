-- Prints the output of a CPSA run as a Prolog database.

-- This programs loads CPSA output.  It assembles the skeletons in the
-- output into a forest of derivation trees.  It then prints the
-- forest in Prolog syntax.  To be loadable by Prolog, the output must
-- be sorted so that clauses of one predicate are colocated.

-- The output should be used by SWI Prolog as strings must not be atoms.
-- Load the generated file using consult/1.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import Data.Char (toLower)
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
      strands h l 0 (alist $ vertex t)
      mapM_ (child h l) (children t)
      mapM_ (dup h l) (seen $ vertex t)

body :: Handle -> Int -> [SExpr Pos] -> IO ()
body h l xs =
    do
      hPutStr h (printf "skel(%d, " l)
      sexprs h xs
      hPutStrLn h ")."

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

sexprs :: Handle -> [SExpr a] -> IO ()
sexprs h [] =
    hPutStr h "[]"
sexprs h (x : xs) =
    do
      hPutStr h "["
      sexpr h x
      rest h xs
      hPutStr h "]"

sexpr :: Handle -> SExpr a -> IO ()
sexpr h (S _ []) = -- This should never happen
    hPutStr h []
sexpr h (S _ (c : s)) = -- Ensure symbol is a Prolog constant
    hPutStr h (map toUnderScore (toLower c : s))
sexpr h (Q _ q) =
    do
      hPutStr h "\""
      hPutStr h q
      hPutStr h "\""
sexpr h (N _ n) =
    hPutStr h (printf "%d" n)
sexpr h (L _ xs) =
    sexprs h xs

toUnderScore :: Char -> Char
toUnderScore '-' = '_'
toUnderScore c = c

rest :: Handle -> [SExpr a] -> IO ()
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
      let lab = label $ vertex t
      hPutStrLn h (printf "child(%d, %d)." l lab)
      case assoc "operation" (alist $ vertex t) of
        Just op ->
            do
              hPutStr h (printf "step(%d, " l) --
              sexpr h (L () (S () "operation" : map strip op))
              hPutStrLn h (printf ", %d)." lab)
              tree h t
        _ ->
            do
              hPutStrLn h (printf "step(%d, [], %d)." l lab)
              tree h t

dup :: Handle -> Int -> (Int, SExpr a) -> IO ()
dup h l (lab, op) | l == lab = return () -- Ignore self loops
dup h l (lab, op) =
    do
      hPutStr h (printf "step(%d, " l)
      sexpr h op
      hPutStrLn h (printf ", %d)." lab)
