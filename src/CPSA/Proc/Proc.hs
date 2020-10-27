-- Reader for defproc

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Proc.Proc (
  parse, Var, Sort, Decl, Stmt(..), Expr(..),
  Proc, mkProc, name, inputs, outputs, stmts, Item(..)) where

import CPSA.Lib.SExpr

-- Abstract syntax for the input language

-- Variable
type Var = String

type Sort = String

-- A declaration, is a variable and a sort
type Decl = (Var, Sort)

-- A procedure
data Proc
  = Proc { name :: String,
           inputs :: [Decl],
           outputs :: [Sort],
           stmts :: [Stmt] }

mkProc :: String  -> [Decl] -> [Sort] -> [Stmt] -> Proc
mkProc name inputs outputs stmts =
  Proc { name = name,
         inputs = inputs,
         outputs = outputs,
         stmts = stmts }

-- A statement
data Stmt
  = Send String Var Var         -- Send a message
  | Bind Decl Expr              -- Bind a variable to an expression
  | Same String Var Var         -- Are two values the same?
  | Return [Var]                -- Return values from the procedure
  | Comment String              -- Insert a comment

-- Expressions
data Expr
  = Call Var [Var]
  | Tagg String

data Item
  = Cmt Pos String
  | Defproc Pos Proc

parse :: [SExpr Pos] -> IO [Item]
parse xs = mapM parseItem xs

parseItem :: SExpr Pos -> IO Item
parseItem (L pos [S _ "comment", Q _ comment]) =
  return $ Cmt pos comment
parseItem (L pos (S _ "defproc" : S _ name : L _ inputs :
               L _ outputs : xs)) =
  do
    inputs <- mapM parseDecl inputs
    outputs <- mapM parseString outputs
    stmts <- mapM parseStmt xs
    return $ Defproc pos $ mkProc name inputs outputs stmts
parseItem x =
  fail (shows (annotation x) "Unrecogized S-Expression")

parseDecl :: SExpr Pos -> IO Decl
parseDecl (L _ [S _ name, S _ sort]) =
  return (name, sort)
parseDecl x =
  fail (shows (annotation x) "Expecting a declaration")

parseString :: SExpr Pos -> IO String
parseString (S _ sort) =
  return sort
parseString x =
  fail (shows (annotation x) "Expecting a string")

parseStmt :: SExpr Pos -> IO Stmt
parseStmt (L _ [S _ "let", L _ [S _ var, S _ sort], expr]) =
  do
    expr <- parseExpr expr
    return $ Bind (var, sort) expr
parseStmt (L _ [S _ send, S _ chan, S _ msg])
  | prefix "send_" send =
    return $ Send send chan msg
parseStmt (L _ [S _ same, S _ x, S _ y])
  | prefix "same_" same =
    return $ Same same x y
parseStmt (L _ (S _ "return" : xs)) =
  do
    returns <- mapM parseString xs
    return $ Return returns
parseStmt (L _ [S _ "comment", Q _ comment]) =
  return $ Comment comment
parseStmt x =
  fail (shows (annotation x) "Malformed statement")

prefix :: String -> String -> Bool
prefix [] _ = True
prefix _ [] = False
prefix (x : xs) (y : ys) = x == y && prefix xs ys

parseExpr :: SExpr Pos -> IO Expr
parseExpr (Q _ tag) =
  return $ Tagg tag
parseExpr (L _ (x : xs)) =
  do
    string <- parseString x
    strings <- mapM parseString xs
    return $ Call string strings
parseExpr x =
  fail (shows (annotation x) "Malformed expression")
