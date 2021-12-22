-- Main routine for cpsa4roletranhs

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import Control.Monad
import Data.Char (toUpper)
import Data.List (intersperse)
import CPSA.Lib.Entry
import CPSA.Lib.Expand
import CPSA.Proc.AltProc

btype :: String
btype = "m"

rt :: String
rt = "rt"

main :: IO ()
main =
    do
      (p, (output, _)) <- start filterOptions filterInterp
      sexprs <- readSExprs p
      items <- tryRun (parse sexprs)
      h <- outputHandle output
      tryRun (emit h items)
      hClose h

tryRun :: IO a -> IO a
tryRun x =
  do
    y <- tryIO x
    case y of
      Right z -> return z
      Left err -> abort err

-- Emitter

emit :: Handle -> [Item] -> IO ()
emit _ [] = fail "empty input"
emit h (Cmt _ comment : xs) =
  do
    hPutStrLn h ("-- " ++  comment)
    hPutStrLn h ""
    let name = getName comment
    hPutStr h "module "
    hPutStr h name
    hPutStrLn h " where"
    hPutStrLn h ""
    hPutStrLn h "import System.IO (Handle)"
    hPutStrLn h "import CPSA.Haskell.Runtime"
    emitProcs h xs
emit _ (Defproc pos _ : _) = fail (shows pos "Expecting a comment")

-- Get protocol name

getName :: String -> String
getName cmt =
  capitalize name
  where
    (name, _) = span (/= ' ') $ drop (length "Protocol: ") cmt

capitalize :: String -> String
capitalize [] = []
capitalize (h : t) = toUpper h : t

emitProcs :: Handle -> [Item] -> IO ()
emitProcs _  [] = return ()
emitProcs h (Cmt _ comment : x : xs) =
  do
    hPutStrLn h ""
    hPutStrLn h ("-- " ++  comment)
    hPutStrLn h ""
    emitProc h x
    emitProcs h xs
emitProcs _ [Cmt pos _] =
  fail (shows pos "Expecting a comment followed by a defproc")
emitProcs _ (Defproc pos _ : _) = fail (shows pos "Expecting a comment")

emitProc :: Handle -> Item -> IO ()
emitProc h (Defproc _ proc) =
  do
    emitSig h proc
    emitHeader h (name proc) (inputs proc)
    mapM_ (emitStmt h) (stmts proc)
emitProc _ (Cmt pos _) =
  fail (shows pos "Expecting a defproc")

emitSig :: Handle -> Proc -> IO ()
emitSig h proc =
  do
    hPutStr h (name proc)
    hPutStr h " :: Runtime r m => r -> "
    mapM_ (emitSigInput h) (inputs proc)
    emitSigOutputs h (length $ outputs proc)

emitSigInput :: Handle -> Decl -> IO ()
emitSigInput h (_, Chan) =
  hPutStr h "Handle -> "
emitSigInput h (_, _) =
  do
    hPutStr h btype
    hPutStr h " -> "

emitSigOutputs :: Handle -> Int -> IO ()
emitSigOutputs h 0 = hPutStrLn h "IO ()"
emitSigOutputs h 1 =
  do
    hPutStr h "IO "
    hPutStrLn h btype
emitSigOutputs h n =
  do
    hPutStr h "IO ("
    hPutStr h btype
    replicateM_ (n - 1) (emitSigOutput h)
    hPutStrLn h ")"

emitSigOutput :: Handle -> IO ()
emitSigOutput h =
  do
    hPutStr h ", "
    hPutStr h btype

emitHeader :: Handle -> String -> [Decl] -> IO ()
emitHeader h name inputs =
  do
    hPutStr h name
    hPutStr h " rt "
    mapM_ (emitInput h) inputs
    hPutStrLn h "="
    hPutStrLn h "  do"
    mapM_ (emitHeaderCheck h) inputs

emitInput :: Handle -> Decl -> IO ()
emitInput h (var, _) =
  do
    hPutStr h var
    hPutStr h " "

emitHeaderCheck :: Handle -> Decl -> IO ()
emitHeaderCheck _ (_, Chan) =
  return ()
emitHeaderCheck h (var, kind) =
  do
    hPutStr h "    rt <- chck rt "
    hPutStr h (show kind)
    hPutStr h " "
    hPutStrLn h var

emitArg :: Handle -> String -> IO ()
emitArg h x =
  hPutStr h (" " ++ x)

emitArgs :: Handle -> [String] -> IO ()
emitArgs h xs =
  mapM_ (emitArg h) xs

emitStmt :: Handle -> Stmt -> IO ()
emitStmt h (Bind (var, kind) expr) =
  do
    hPutStr h "    ("
    hPutStr h var
    hPutStr h ", rt) <-"
    emitExpr h expr
    emitHeaderCheck h (var, kind)
emitStmt h (Send chan (msg, kind)) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "send", rt, show kind, chan, msg]
    hPutStrLn h ""
emitStmt h (Same kind x y) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "same", rt, show kind, x, y]
    hPutStrLn h ""
emitStmt h (Ltkp x y z) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "ltkp", rt, x, y, z]
    hPutStrLn h ""
emitStmt h (Invp kind x y) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "invp", rt, show kind, x, y]
    hPutStrLn h ""
emitStmt h (Namp kind x y) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "namp", rt, show kind, x, y]
    hPutStrLn h ""
emitStmt h (Nm2p kind x y z) =
  do
    hPutStr h "   "
    emitArgs h ["rt <-", "nm2p", rt, show kind, x, y, z]
    hPutStrLn h ""
emitStmt h (Return returns) =
  do
    hPutStrLn h "    let _ = rt"
    hPutStr h "    return "
    emitReturns h returns
emitStmt h (Comment comment) =
  hPutStrLn h ("    -- " ++  comment)

emitReturns :: Handle -> [String] -> IO ()
emitReturns h [] =
  hPutStrLn h "()"
emitReturns h [x] =
  hPutStrLn h x
emitReturns h xs =
  do
    hPutStr h "("
    mapM_ (hPutStr h) (intersperse ", " xs)
    hPutStrLn h ")"

emitExpr :: Handle -> Expr -> IO ()
emitExpr h (PairE (x, left) (y, right)) =
  do
    emitArgs h ["pair", rt, show left, show right, x, y]
    hPutStrLn h ""
emitExpr h (Frst kind x) =
  do
    emitArgs h ["frst", rt, show kind, x]
    hPutStrLn h ""
emitExpr h (Scnd kind x) =
  do
    emitArgs h ["scnd", rt, show kind, x]
    hPutStrLn h ""
emitExpr h (Encr (x, left) (y, right)) =
  do
    emitArgs h ["encr", rt, show left, show right, x, y]
    hPutStrLn h ""
emitExpr h (Decr left x (y, right)) =
  do
    emitArgs h ["decr", rt, show left, show right, x, y]
    hPutStrLn h ""
emitExpr h (Tag x) =
  hPutStrLn h (" tag rt \"" ++ x ++ "\"")
emitExpr h (HashE (x, kind)) =
  do
    emitArgs h ["hash", rt, show kind, x]
    hPutStrLn h ""
emitExpr h (Frsh kind) =
  do
    emitArgs h ["frsh", rt, show kind]
    hPutStrLn h ""
emitExpr h (Recv kind x) =
  do
    emitArgs h ["recv", rt, show kind, x]
    hPutStrLn h ""
