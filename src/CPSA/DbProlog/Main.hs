-- Prints the database from a CPSA run as a Prolog database.

-- To be loadable by Prolog, the output must be sorted so that clauses
-- of one predicate are colocated.

-- The output should be used by SWI Prolog as strings must not be atoms.
-- Load the generated file using consult/1.

-- Copyright (c) 2024 The MITRE Corporation
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

main :: IO ()
main =
    do
      (p, (output, _)) <- start filterOptions filterInterp
      h <- outputHandle output
      dbProlog p h
      hClose h

dbProlog :: PosHandle -> Handle -> IO ()
dbProlog p h =
    do
      x <- gentlyReadSExpr p
      case x of
        Nothing -> return ()
        Just x ->
            do
              display h x
              dbProlog p h

display :: Handle -> SExpr Pos -> IO ()
display h (L _ [S _ "comment", Q _ comment]) =
    hPutStrLn h ("%% " ++ comment)
display _ (L _ (S _ "comment" : _)) =
    return ()
display h (L _ (S _ pred : x : xs)) =
    do
      hPutStr h (toPIdent pred)
      hPutStr h "("
      sexpr h x
      rest h xs
      hPutStrLn h ")."
display _ _ =
    return ()

toPIdent :: String -> String
toPIdent [] = []
toPIdent (c:s) = map toUnderScore (toLower c : s)

sexprs :: Handle -> [SExpr a] -> IO ()
sexprs h [] =
    hPutStr h "[]"
sexprs h (x : xs) =
    do
    --   hPutStr h "["
      sexpr h x
      rest h xs
    --   hPutStr h "]"

sexpr :: Handle -> SExpr a -> IO ()
sexpr h (S _ []) = -- This should never happen
    hPutStr h []
sexpr h (S _ s) = -- Ensure symbol is a Prolog constant
    hPutStr h (toPIdent s)
sexpr h (Q _ q) =
    do
      hPutStr h "\""
      hPutStr h q
      hPutStr h "\""
sexpr h (N _ n) =
    hPutStr h (printf "%d" n)
sexpr h (L _ ((S _ x):xs)) =
    do
        hPutStr h (toPIdent x)
        hPutStr h "("
        sexprs h xs
        hPutStr h ")"
sexpr h (L _ xs) = 
    do 
        hPutStr h "["
        sexprs h xs
        hPutStr h "]"

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
