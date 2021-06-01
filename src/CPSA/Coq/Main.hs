-- Main routine for cpsa4coq

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import Data.Char (toUpper)
import Data.List (intersperse)
import CPSA.Lib.Entry
import CPSA.Lib.Expand
import CPSA.Proc.Proc

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      sexprs <- readSExprs p
      items <- tryRun (parse sexprs)
      h <- outputHandle output
      tryRun (emit h margin items)
      hClose h

tryRun :: IO a -> IO a
tryRun x =
  do
    y <- tryIO x
    case y of
      Right z -> return z
      Left err -> abort err

-- Emitter

emit :: Handle -> Int -> [Item] -> IO ()
emit _ _ [] = fail "empty input"
emit h margin (Cmt _ comment : xs) =
  do
    hPutStrLn h ("(** " ++  comment ++ " *)")
    hPutStrLn h ""
    hPutStrLn h "Require Import Proc."
    hPutStrLn h "Import List.ListNotations."
    hPutStrLn h "Open Scope list_scope."
    hPutStrLn h "Open Scope string."
    emitProcs h margin xs
emit _ _ (Defproc pos _ : _) = fail (shows pos "Expecting a comment")

emitProcs :: Handle -> Int -> [Item] -> IO ()
emitProcs _ _ [] = return ()
emitProcs h margin (Cmt _ comment : x : xs) =
  do
    hPutStrLn h ""
    hPutStrLn h ("(** " ++  comment ++ " *)")
    hPutStrLn h ""
    emitProc h margin x
    emitProcs h margin xs
emitProcs _ _ [Cmt pos _] =
  fail (shows pos "Expecting a comment followed by a defproc")
emitProcs _ _ (Defproc pos _ : _) = fail (shows pos "Expecting a comment")

emitProc :: Handle -> Int -> Item -> IO ()
emitProc h margin (Defproc _ proc) =
  do
    emitHeader h margin (name proc) (inputs proc)
    mapM_ (emitStmt h margin) (stmts proc)
    hPutStrLn h "  ]."
emitProc _ _ (Cmt pos _) =
  fail (shows pos "Expecting a defproc")

emitHeader :: Handle -> Int -> String -> [Decl] -> IO ()
emitHeader h margin name inputs =
  do
    hPutStrLn h ("Definition " ++ name ++ ": proc :=")
    hPutStrLn h "  mkProc"
    emitInputs h margin (map emitInput inputs)
    hPutStrLn h "  ["

emitInput :: Decl -> String
emitInput (var, kind) =
  "(" ++ ref var ++ ", " ++ toKind kind ++ ")"

ref :: String -> String
ref [] = []
ref (_ : xs) = xs

toKind :: String -> String
toKind [] = []
toKind (h : t) = toUpper h : t

emitInputs :: Handle -> Int -> [String] -> IO ()
emitInputs h _ [] =
  hPutStrLn h "  []"
emitInputs h _ xs =
  do
    hPutStr h "  ["
    mapM_ (hPutStr h) (intersperse "; " xs)
    hPutStrLn h "]"

emitStmt :: Handle -> Int -> Stmt -> IO ()
emitStmt h _ (Bind (var, kind) expr) =
  do
    hPutStr h ("   Bind (" ++ ref var ++ ", " ++ toKind kind ++ ") ")
    emitExpr h expr
    hPutStrLn h  ";"
emitStmt h _ (Send _ chan msg) =
  hPutStrLn h ("   Send " ++ ref chan ++ " " ++ ref msg ++ ";")
emitStmt h _ (Same _ x y) =
  hPutStrLn h ("   Same " ++ ref x ++ " " ++ ref y ++ ";")
emitStmt h _ (Ltkp _ x y z) =
  hPutStrLn h ("   Ltkp " ++ ref x ++ " " ++ ref y ++
               " " ++ ref z ++ ";")
emitStmt h _ (Invp _ x y) =
  hPutStrLn h ("   Invp " ++ ref x ++ " " ++ ref y ++ ";")
emitStmt h _ (Namp _ x y) =
  hPutStrLn h ("   Namp " ++ ref x ++ " " ++ ref y ++ ";")
emitStmt h _ (Nm2p _ x y z) =
  hPutStrLn h ("   Nm2p " ++ ref x ++ " " ++
                          ref y ++ " " ++ ref z ++ ";")
emitStmt h margin (Return returns) =
  do
    hPutStr h "   Return "
    emitReturns h margin (map ref returns)
emitStmt h _ (Comment comment) =
  hPutStrLn h ("   (* " ++  comment ++ " *)")

emitExpr :: Handle -> Expr -> IO ()
emitExpr h (Call op args) =
  do
    hPutStr h "("
    hPutStr h $ trim $ toKind op
    mapM_ (emitArg h) args
    hPutStr h ")"
emitExpr h (Tag x) =
  hPutStr h ("(Quot_ \"" ++ x ++ "\")")

trim :: String -> String
trim [] = []
trim ('_' : _) = "_"
trim (x : xs) = x : trim xs

emitArg :: Handle -> String -> IO ()
emitArg h x =
  hPutStr h (" " ++ ref x)

emitReturns :: Handle -> Int -> [String] -> IO ()
emitReturns h _ [] =
  hPutStrLn h "[]"
emitReturns h _ xs =
  do
    hPutStr h "["
    mapM_ (hPutStr h) (intersperse "; " xs)
    hPutStrLn h "]"
