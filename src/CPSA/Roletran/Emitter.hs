-- Emits generated code

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Roletran.Emitter (
  Proc, mkProc, name, pos,
  Vari, Decl, Stmt(..), Expr(..),
  emit, displayPos) where

import CPSA.Lib.SExpr
import CPSA.Lib.Pretty
import CPSA.Roletran.Algebra (Sort(..))
import CPSA.Roletran.Displayer (displaySort)

-- When true, add the sort of a let bound variable
showBindSort :: Bool
showBindSort = True

-- Variable index
type Vari = Int

-- A declaration, comprising an index for a variable and the sort of
-- that variable
type Decl = (Vari, Sort)

-- A procedure
data Proc
  = Proc { name :: String,
           pos :: Pos,
           inputs :: [Decl],
           firstVar :: Vari,
           outputs :: [Sort],
           stmts :: [Stmt] }

mkProc :: String -> Pos -> [Decl] -> [Sort] -> [Stmt] -> Proc
mkProc name pos inputs outputs stmts =
  Proc { name = name,
         pos = pos,
         inputs = inputs,
         firstVar = length inputs,
         outputs = outputs,
         stmts = stmts }

-- A statement
data Stmt
  = Recv Decl Vari              -- Receive a message
  | Send Vari Decl              -- Send a message
  | Bind Decl Expr              -- Bind a variable to an expression
  | Same Sort Vari Vari         -- Are two values the same?
  | Return [Vari]               -- Return values from the procedure
  | Comment String              -- Insert a comment

-- Expressions
data Expr
  = Pair Decl Decl              -- Construct a pair
  | Frst Sort Vari              -- project first component of pair
  | Scnd Sort Vari              -- project second component of pair
  | Encr Decl Decl              -- Encrypt plain text
  | Decr Sort Vari Decl         -- Decrypt cipher text
  | Tagg String                 -- Construct a tag
  | Hash Decl                   -- Construct a hash
  | Nonce Sort                  -- Generate a nonce

-- Emit code as a pretty printed S-expression

emit :: Int -> Proc -> Pretty
emit indent proc =
  grp indent (displayHeader indent proc :
               displayStmts (firstVar proc) (stmts proc))

displayHeader :: Int -> Proc -> Pretty
displayHeader indent proc =
  blo (2 * indent)
  [str "(defproc ", str (dehyphen $ name proc),
    brk 1, str "(", grp 0 (displayInputs (firstVar proc) (inputs proc)),
    brk 1, str "(", grp 0 (displayOutputs (outputs proc))]

dehyphen :: String -> String
dehyphen [] = []
dehyphen ('-' : cs) = '_' : dehyphen cs
dehyphen (c : cs) = c : dehyphen cs

displayInputs :: Vari -> [Decl] -> [Pretty]
displayInputs _ [] = [str ")"]
displayInputs first (d : ds) =
  displayInput first d : foldr f [str ")"] ds
  where
    f d ps = brk 1 : displayInput first d : ps

displayInput :: Vari -> Decl -> Pretty
displayInput first (x, s) =
  str ("(" ++ var first x ++ " " ++ displaySort s ++ ")")

displayOutputs :: [Sort] -> [Pretty]
displayOutputs [] = [str ")"]
displayOutputs (s : ss) =
  str (displaySort s) : foldr f [str ")"] ss
  where
    f s ps = brk 1 : str (displaySort s) : ps

displayStmts :: Vari -> [Stmt] -> [Pretty]
displayStmts _ [] = [str ")"]
displayStmts first (s : ss) =
  brk 1 : str (displayStmt first s) : displayStmts first ss

displayStmt :: Vari -> Stmt -> String
displayStmt first (Recv d c) =
  "(let " ++ bvar first d ++ mark " (recv" [snd d] ++
  " " ++ var first c ++ "))"
displayStmt first (Send c (x, s)) =
  mark "(send" [s] ++ " " ++ var first c ++
  " " ++ var first x ++ ")"
displayStmt first (Bind d e) =
  "(let " ++ bvar first d ++ " " ++
  displayExpr first e ++ ")"
displayStmt first (Same s x y) =
  mark "(same" [s] ++ " " ++ var first x ++
  " " ++ var first y ++ ")"
displayStmt first (Return vs) =
  "(return" ++ foldr f ")" vs
  where
    f v str = " " ++ var first v ++ str
displayStmt _ (Comment cmt) =
  "(comment \"" ++ cmt ++ "\")"

displayExpr :: Vari -> Expr -> String
displayExpr first (Pair (x, s) (y, t)) =
  mark "(pair" [s, t] ++ " " ++
  var first x ++ " " ++ var first y ++ ")"
displayExpr first (Frst s x) =
  mark "(frst" [s] ++ " " ++ var first x ++ ")"
displayExpr first (Scnd s x) =
  mark "(scnd" [s] ++ " " ++ var first x ++ ")"
displayExpr first (Encr (x, s) (y, t)) =
  mark "(encr" [s, t] ++ " " ++
  var first x ++ " " ++ var first y ++ ")"
displayExpr first (Decr s x (y, t)) =
  mark "(decr" [s, inv t] ++ " " ++
  var first x ++ " " ++ var first y ++ ")"
displayExpr _ (Tagg s) = "\"" ++ s ++ "\""
displayExpr first (Hash (x, s)) =
  mark "(hash" [s] ++ " " ++ var first x ++ ")"
displayExpr _ (Nonce s) =
  mark "(nonce" [s] ++ ")"

-- Display parameters with variables that start with 'p'.
-- Display let bound variables starting with 'v'.
var :: Vari -> Vari -> String
var first v
  | v < first = 'p' : show v
  | otherwise = 'v' : show v

-- Maybe show sort for a let bound variable.
bvar :: Vari -> Decl -> String
bvar first (v, s)
  | showBindSort =
    "(" ++ var first v ++ " " ++ displaySort s ++ ")"
  | otherwise = var first v

-- Mark a symbol with some sort abbeviations.
mark :: String -> [Sort] -> String
mark sym sorts =
  sym ++ "_" ++ map abbrev sorts

abbrev :: Sort -> Char
abbrev Text = 't'
abbrev Data = 'd'
abbrev Name = 'n'
abbrev Skey = 's'
abbrev Akey = 'a'
abbrev Ikey = 'i'
abbrev Mesg = 'm'
abbrev Chan = 'c'

-- The inverse sort of a sort
inv :: Sort -> Sort
inv Text = Text
inv Data = Data
inv Name = Name
inv Skey = Skey
inv Akey = Ikey
inv Ikey = Akey
inv Mesg = Mesg
inv Chan = Chan

-- Trim last two characters when showing a Pos.
displayPos :: Pos -> String
displayPos pos =
  f $ show pos
  where
    f "" = ""
    f ": " = ""
    f (c : cs) = c : f cs
