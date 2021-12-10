-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Proc.AltProc (
  parse, Var, Type(..), Decl, Stmt(..), Expr(..),
  Proc, mkProc, name, inputs, outputs, stmts, Item(..)) where

import CPSA.Lib.SExpr

-- Abstract syntax for the input language

-- Variable
type Var = String

-- Types of messages
data Type
  = Text                        -- Plaintext
  | Data                        -- Data
  | Name                        -- Name
  | Skey                        -- Symmetric key
  | Akey                        -- Public asymmetric key
  | Ikey                        -- Private asymmetric key
  | Chan                        -- Channel
  | Mesg                        -- Message -- top kind for terms
  | Quot                        -- Tag
  | Pair                        -- Pair
  | Senc                        -- Symmetric encryption
  | Aenc                        -- Asymmetric encryption
  | Ienc                        -- Sign
  | Hash                        -- Hash
  deriving Show

-- A declaration, is a variable and a type
type Decl = (Var, Type)

-- A procedure
data Proc
  = Proc { name :: String,
           inputs :: [Decl],
           outputs :: [Type],
           stmts :: [Stmt] }

mkProc :: String  -> [Decl] -> [Type] -> [Stmt] -> Proc
mkProc name inputs outputs stmts =
  Proc { name = name,
         inputs = inputs,
         outputs = outputs,
         stmts = stmts }

-- A statement
data Stmt
  = Bind Decl Expr              -- Bind a variable to an expression
  | Send Var Decl               -- Send a message
  | Same Type Var Var           -- Are two values the same?
  | Ltkp Var Var Var            -- Vars related by the ltk function?
  | Invp Type Var Var           -- Vars related by the invk function?
  | Namp Type Var Var           -- Vars related by the pubk function?
  | Nm2p Type Var Var Var       -- Vars related by the pubk2 function?
  | Return [Var]                -- Return values from the procedure
  | Comment String              -- Insert a comment

-- For Invp, Namp, and Nm2p, the type is associated with the first
-- variable.  A name is associated with the second two variables in
-- Ltkp, the second variable in Namp, and the third variable in Nm2p.
-- A tag is associated with the second variable in Nm2p.

-- Expressions -- The type is associated with the returned value
data Expr
  = PairE Decl Decl             -- Construct a pair
  | Frst Type Var               -- project first component of pair
  | Scnd Type Var               -- project second component of pair
  | Encr Decl Decl              -- Encrypt plain text
  | Decr Type Var Decl          -- Decrypt cipher text
  | Tag String                  -- Construct a tag
  | HashE Decl                  -- Construct a hash
  | Frsh Type                   -- Generate a fresh nonce
  | Recv Type Var               -- Receive a message

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
    outputs <- mapM parseOutput outputs
    stmts <- mapM parseStmt xs
    return $ Defproc pos $ mkProc name inputs outputs stmts
parseItem x =
  fail (shows (annotation x) "Unrecogized S-Expression")

parseDecl :: SExpr Pos -> IO Decl
parseDecl (L _ [S _ name, S pos kind]) =
  do
    kind <- parseType pos kind
    return (name, kind)
parseDecl x =
  fail (shows (annotation x) "Expecting a declaration")

parseType :: Pos -> String -> IO Type
parseType _ "text" = return Text
parseType _ "data" = return Data
parseType _ "name" = return Name
parseType _ "skey" = return Skey
parseType _ "akey" = return Akey
parseType _ "ikey" = return Ikey
parseType _ "chan" = return Chan
parseType _ "mesg" = return Mesg
parseType _ "quot" = return Quot
parseType _ "pair" = return Pair
parseType _ "senc" = return Senc
parseType _ "aenc" = return Aenc
parseType _ "ienc" = return Ienc
parseType _ "hash" = return Hash
parseType pos s = fail (shows pos ("Unrecognized type: " ++ s))

abbrev :: Pos -> Char -> IO Type
abbrev _ 't' = return Text
abbrev _ 'd' = return Data
abbrev _ 'n' = return Name
abbrev _ 's' = return Skey
abbrev _ 'a' = return Akey
abbrev _ 'i' = return Ikey
-- Note channel is missing
abbrev _ 'm' = return Mesg
abbrev _ 'q' = return Quot
abbrev _ 'p' = return Pair
abbrev _ 'e' = return Senc
abbrev _ 'y' = return Aenc
abbrev _ 'z' = return Ienc
abbrev _ 'h' = return Hash
abbrev pos ch = fail (shows pos ("Bad abbreviation '" ++ [ch] ++ "'"))

opType :: Pos -> String -> IO (String, [Type])
opType pos op =
  do
    types <- mapM (abbrev pos) kinds
    return (inst, types)
    where
      (inst, kinds) = opAbbrev op

opAbbrev :: String -> (String, String)
opAbbrev op =
  f [] op
  where
    f acc [] = (reverse acc, [])
    f acc ('_' : op) = (reverse acc, op)
    f acc (ch : op) = f (ch : acc) op

parseOutput :: SExpr Pos -> IO Type
parseOutput (S pos sym) = parseType pos sym
parseOutput x =
  fail (shows (annotation x) "Expecting a symbol")

parseStmt :: SExpr Pos -> IO Stmt
parseStmt (L posL (S posS op : xs)) =
  do
    (keyword, types) <- opType posS op
    case keyword of
      "let" -> parseLet posL types xs
      "send" -> parseSend posL types xs
      "same" -> parseSame posL types xs
      "ltk" -> parseLtk posL types xs
      "invp" -> parseInvp posL types xs
      "namp" -> parseNamp posL types xs
      "nm2p" -> parseNm2p posL types xs
      "return" -> parseReturn posL types xs
      "comment" -> parseComment posL types xs
      _ -> fail (shows posS ("Unreconized statement: " ++ keyword))
parseStmt x =
  fail (shows (annotation x) "Malformed statement")

parseLet :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseLet _ [] [L _ [S _ var, S pos kind], expr] =
  do
    expr <- parseExpr expr
    kind <- parseType pos kind
    return $ Bind (var, kind) expr
parseLet pos _ _ = fail (shows pos "Malformed let")

parseSend :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseSend _ [kind] [S _ chan, S _ msg] =
  return $ Send chan (msg, kind)
parseSend pos _ _ = fail (shows pos "Malformed send")

parseSame :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseSame _ [kind] [S _ x, S _ y] =
  return $ Same kind x y
parseSame pos _ _ = fail (shows pos "Malformed same")

parseLtk :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseLtk _ [] [S _ x, S _ y, S _ z] =
  return $ Ltkp x y z
parseLtk pos _ _ = fail (shows pos "Malformed ltkp")

parseInvp :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseInvp _ [kind] [S _ x, S _ y] =
  return $ Invp kind x y
parseInvp pos _ _ = fail (shows pos "Malformed invp")

parseNamp :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseNamp _ [kind] [S _ x, S _ y] =
  return $ Namp kind x y
parseNamp pos _ _ = fail (shows pos "Malformed namp")

parseNm2p :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseNm2p _ [kind] [S _ x, S _ y, S _ z] =
  return $ Nm2p kind x y z
parseNm2p pos _ _ = fail (shows pos "Malformed nmp2")

parseReturn :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseReturn _ [] xs =
  do
    vars <- mapM parseString xs
    return $ Return vars
parseReturn pos _ _ = fail (shows pos "Malformed return")

parseString :: SExpr Pos -> IO String
parseString (S _ sym) = return sym
parseString x =
  fail (shows (annotation x) "Expecting a symbol")

parseComment :: Pos -> [Type] -> [SExpr Pos] -> IO Stmt
parseComment _ [] [Q _ comment] =
  return $ Comment comment
parseComment pos _ _ = fail (shows pos "Malformed comment")

parseExpr :: SExpr Pos -> IO Expr
parseExpr (Q _ tag) =
  return $ Tag tag
parseExpr (L posL (S posS op : xs)) =
  do
    (keyword, types) <- opType posS op
    case keyword of
      "pair" -> parsePair posL types xs
      "frst" -> parseFrst posL types xs
      "scnd" -> parseScnd posL types xs
      "encr" -> parseEncr posL types xs
      "decr" -> parseDecr posL types xs
      "frsh" -> parseFrsh posL types xs
      "hash" -> parseHash posL types xs
      "recv" -> parseRecv posL types xs
      _ -> fail (shows posS ("Unreconized expression: " ++ keyword))
parseExpr x =
  fail (shows (annotation x) "Malformed expression")

parsePair :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parsePair _ [left, right] [S _ x, S _ y] =
  return $ PairE (x, left) (y, right)
parsePair pos _ _ = fail (shows pos "Malformed pair")

parseFrst :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseFrst _ [kind] [S _ x] =
  return $ Frst kind x
parseFrst pos _ _ = fail (shows pos "Malformed frst")

parseScnd :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseScnd _ [kind] [S _ x] =
  return $ Scnd kind x
parseScnd pos _ _ = fail (shows pos "Malformed scnd")

parseEncr :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseEncr _ [left, right] [S _ x, S _ y] =
  return $ Encr (x, left) (y, right)
parseEncr pos _ _ = fail (shows pos "Malformed encr")

parseDecr :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseDecr _ [left, right] [S _ x, S _ y] =
  return $ Decr left x (y, right)
parseDecr pos _ _ = fail (shows pos "Malformed decr")

parseHash :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseHash _ [kind] [S _ x] =
  return $ HashE (x, kind)
parseHash pos _ _ = fail (shows pos "Malformed hash")

parseFrsh :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseFrsh _ [kind] [] =
  return $ Frsh kind
parseFrsh pos _ _ = fail (shows pos "Malformed frsh")

parseRecv :: Pos -> [Type] -> [SExpr Pos] -> IO Expr
parseRecv _ [kind] [S _ x] =
  return $ Recv kind x
parseRecv pos _ _ = fail (shows pos "Malformed recv")
