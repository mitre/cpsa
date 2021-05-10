-- Emits generated code

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Roletran.Emitter (
  Kind(..), kind, Proc, mkProc, name, pos,
  Vari, Decl, Stmt(..), Expr(..),
  emit, displayPos) where

import CPSA.Lib.SExpr
import CPSA.Lib.Pretty
import CPSA.Roletran.Algebra (Term(..))

data Kind
  = KText                       -- Plaintext
  | KData                       -- Data
  | KName                       -- Name
  | KSkey                       -- Symmetric key
  | KAkey                       -- Public asymmetric key
  | KIkey                       -- Private asymmetric key
  | KMesg                       -- Message -- top kind for terms
  | KQuot                       -- Tag
  | KPair                       -- Pair
  | KSenc                       -- Symmetric encryption
  | KAenc                       -- Asymmetric encryption
  | KIenc                       -- Sign
  | KHash                       -- Hash
  | KChan                       -- Channels -- not allowed
  deriving (Show, Eq)           -- in terms in events

-- Return the kind of a term.
kind :: Term -> Kind
kind (Txt _) = KText
kind (Dta _) = KData
kind (Nam _) = KName
kind (Sky _) = KSkey
kind (Aky _) = KAkey
kind (Iky _) = KIkey
kind (Msg _) = KMesg
kind (Tag _) = KQuot
kind (Pr _ _) = KPair
kind (En _ (Aky _)) = KAenc
kind (En _ (Iky _)) = KIenc
kind (En _ _) = KSenc
kind (Hsh _) = KHash
kind (Chn _) = KChan

-- When true, add the kind of a let bound variable
showBindKind :: Bool
showBindKind = True

-- Variable index
type Vari = Int

-- A declaration, comprising an index for a variable and the kind of
-- that variable
type Decl = (Vari, Kind)

-- A procedure
data Proc
  = Proc { name :: String,
           pos :: Pos,
           inputs :: [Decl],
           firstVar :: Vari,
           outputs :: [Kind],
           stmts :: [Stmt] }

mkProc :: String -> Pos -> [Decl] -> [Kind] -> [Stmt] -> Proc
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
  | Same Kind Vari Vari         -- Are two values the same?
  | Ltkp Vari Vari Vari         -- Values related by the ltk function?
  | Invp Kind Vari Vari         -- Values related by the invk function?
  | Namp Kind Vari Vari         -- Values related by the pubk function?
  | Nm2p Kind Vari Vari Vari    -- Values related by the pubk2 function?
  | Return [Vari]               -- Return values from the procedure
  | Comment String              -- Insert a comment

-- Expressions
data Expr
  = Pair Decl Decl              -- Construct a pair
  | Frst Kind Vari              -- project first component of pair
  | Scnd Kind Vari              -- project second component of pair
  | Encr Decl Decl              -- Encrypt plain text
  | Decr Kind Vari Decl         -- Decrypt cipher text
  | Quot String                 -- Construct a tag
  | Hash Decl                   -- Construct a hash
  | Frsh Kind                   -- Generate a fresh nonce

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
  str ("(" ++ var first x ++ " " ++ displayKind s ++ ")")

displayOutputs :: [Kind] -> [Pretty]
displayOutputs [] = [str ")"]
displayOutputs (s : ss) =
  str (displayKind s) : foldr f [str ")"] ss
  where
    f s ps = brk 1 : str (displayKind s) : ps

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
displayStmt first (Ltkp x y z) =
  "(ltk " ++ var first x ++ " " ++ var first y ++
  " " ++ var first z ++ ")"
displayStmt first (Invp s x y) =
  mark "(invp" [s] ++ " " ++ var first x ++
  " " ++ var first y ++ ")"
displayStmt first (Namp s x y) =
  mark "(namp" [s] ++ " " ++ var first x ++
  " " ++ var first y ++ ")"
displayStmt first (Nm2p s x y z) =
  mark "(nm2p" [s] ++ " " ++ var first x ++
  " " ++ var first y ++ " " ++ var first z ++ ")"
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
displayExpr _ (Quot s) = "\"" ++ s ++ "\""
displayExpr first (Hash (x, s)) =
  mark "(hash" [s] ++ " " ++ var first x ++ ")"
displayExpr _ (Frsh s) =
  mark "(frsh" [s] ++ ")"

-- Display parameters with variables that start with 'p'.
-- Display let bound variables starting with 'v'.
var :: Vari -> Vari -> String
var first v
  | v < first = 'p' : show v
  | otherwise = 'v' : show v

-- Maybe show kind for a let bound variable.
bvar :: Vari -> Decl -> String
bvar first (v, s)
  | showBindKind =
    "(" ++ var first v ++ " " ++ displayKind s ++ ")"
  | otherwise = var first v

-- Mark a symbol with some kind abbeviations.
mark :: String -> [Kind] -> String
mark sym kinds =
  sym ++ "_" ++ map abbrev kinds

displayKind :: Kind -> String
displayKind KText = "text"
displayKind KData = "data"
displayKind KName = "name"
displayKind KSkey = "skey"
displayKind KAkey = "akey"
displayKind KIkey = "ikey"
displayKind KMesg = "mesg"
displayKind KQuot = "quot"
displayKind KPair = "pair"
displayKind KSenc = "senc"
displayKind KAenc = "aenc"
displayKind KIenc = "ienc"
displayKind KHash = "hash"
displayKind KChan = "chan"

abbrev :: Kind -> Char
abbrev KText = 't'
abbrev KData = 'd'
abbrev KName = 'n'
abbrev KSkey = 's'
abbrev KAkey = 'a'
abbrev KIkey = 'i'
abbrev KMesg = 'm'
abbrev KQuot = 'q'
abbrev KPair = 'p'
abbrev KSenc = 'e'
abbrev KAenc = 'y'
abbrev KIenc = 'z'
abbrev KHash = 'h'
abbrev KChan = 'c'

-- The inverse kind of a kind
inv :: Kind -> Kind
inv KAkey = KIkey
inv KIkey = KAkey
inv k = k

-- Trim last two characters when showing a Pos.
displayPos :: Pos -> String
displayPos pos =
  f $ show pos
  where
    f "" = ""
    f ": " = ""
    f (c : cs) = c : f cs
