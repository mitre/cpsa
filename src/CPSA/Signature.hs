-- Signatures for algebras

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Signature (Sig (..), Operator (..),
                       defaultSig, loadSig, findOper) where

import Control.Monad (foldM)
import CPSA.Lib.SExpr (SExpr(..), Pos, annotation)
import Data.List (nub)

-- The data structure used to represent a signature for an algebra

data Sig = Sig
  { atoms :: [String],          -- Sorts that are not "chan" or "locn"
    akeys :: [String],          -- Asymmetric key sorts
    opers :: [Operator] }       -- Operators
  deriving Show

data Operator
  = Enc String                  -- An "enc" like operator
    -- An "enc" like operator for use with symmetric keys
  | Senc String
    -- An "enc" like operator for use with asymmetric keys`
  | Aenc String
    -- An "enc" like operator for use with inverse asymmetric keys
  | Sign String
  | Hash String                 -- A "hash" like operator
  | Tupl String Int             -- A "cat" like operator
  deriving Show

findOper :: String -> [Operator] -> Maybe Operator
findOper _ [] = Nothing
findOper sym (op@(Enc name) : _) | sym == name = Just op
findOper sym (op@(Senc name) : _) | sym == name = Just op
findOper sym (op@(Aenc name) : _) | sym == name = Just op
findOper sym (op@(Sign name) : _) | sym == name = Just op
findOper sym (op@(Hash name) : _) | sym == name = Just op
findOper sym (op@(Tupl name _) : _) | sym == name = Just op
findOper sym (op@(Enc name) : _) | sym == name = Just op
findOper sym (op@(Enc name) : _) | sym == name = Just op
findOper sym (_ : opers) = findOper sym opers

-- The default signature does not mention "cat" because it is handled
-- specially.  The same is true for "mesg".
defaultSig :: Sig
defaultSig = Sig {
  atoms = ["text", "data", "skey", "akey"],
  akeys = ["akey"],
  opers = [Enc("enc"), Hash("hash")]
  }

isValidSig :: Sig -> Bool
isValidSig sig = isValidAtoms sig && isValidOpers (opers sig)

-- Ensure no atom is bad, and every akey is in atoms.
isValidAtoms :: Sig -> Bool
isValidAtoms sig =
  all (\s -> notElem s badAtoms) (atoms sig) &&
  all (\s -> elem s (atoms sig)) (akeys sig)

badAtoms :: [String]
badAtoms = ["mesg", "name", "chan", "locn", "indx", "pval", "strd"]

-- Ensure no operators is a bad operator and that there are no duplicates.
isValidOpers :: [Operator] -> Bool
isValidOpers opers =
  loop [] opers
  where
    loop acc [] =
      length acc == length (nub acc) -- Ensure no duplicates
    loop acc (Enc s : opers) =
      notElem s badOpers && loop (s : acc) opers
    loop acc (Senc s : opers) =
      notElem s badOpers && loop (s : acc) opers
    loop acc (Aenc s : opers) =
      notElem s badOpers && loop (s : acc) opers
    loop acc (Sign s : opers) =
      notElem s badOpers && loop (s : acc) opers
    loop acc (Hash s : opers) =
      notElem s badOpers && loop (s : acc) opers
    loop acc (Tupl s n : opers) =
      notElem s badOpers && n > 0 && loop (s : acc) opers

badOpers :: [String]
badOpers = ["pubk", "privk", "invk", "ltk", "cat"]

-- Load a signature

-- LANG ::= (lang DECL*)
--
-- DECL ::= (SYMBOL+ TYPE)
--
-- TYPE ::= atom | akey | hash | (tupl N)
--       | enc | senc | aenc | sign.

loadSig :: MonadFail m => Pos -> [SExpr Pos] -> m Sig
loadSig pos decls =
  do
    let init = (atoms defaultSig, akeys defaultSig, opers defaultSig)
    (ats, aks, ops) <- foldM loadDecl init decls
    let sig = Sig {
          atoms = nub (aks ++ ats),
          akeys = nub aks,
          opers = ops }
    case isValidSig sig of
      True -> return sig
      False -> fail (shows pos "Invalid signature")

loadDecl :: MonadFail m => ([String], [String], [Operator]) ->
            SExpr Pos -> m ([String], [String], [Operator])
loadDecl (ats, aks, ops) (L pos xs)
  | length xs < 2 = fail (shows pos "Malformed lang field")
  | otherwise =
    do
      typ <- loadType (last xs)
      syms <- mapM loadSym (init xs)
      case typ of
        TAtom -> return (syms ++ ats, aks, ops)
        TAkey -> return (ats, syms ++ aks, ops)
        TEnc -> return (ats, aks, map Enc syms ++ ops)
        TSenc -> return (ats, aks, map Senc syms ++ ops)
        TAenc -> return (ats, aks, map Aenc syms ++ ops)
        TSign -> return (ats, aks, map Sign syms ++ ops)
        THash -> return (ats, aks, map Hash syms ++ ops)
        TTupl n -> return (ats, aks, map (\s -> Tupl s n) syms ++ ops)
loadDecl _ x =
  fail (shows (annotation x) "Malformed lang field")

data Type
  = TAtom
  | TAkey
  | TEnc
  | TSenc
  | TAenc
  | TSign
  | THash
  | TTupl Int

loadType :: MonadFail m => SExpr Pos -> m Type
loadType (S pos sym) =
  case sym of
    "atom" -> return TAtom
    "akey" -> return TAkey
    "enc" -> return TEnc
    "senc" -> return TSenc
    "aenc" -> return TAenc
    "sign" -> return TSign
    "hash" -> return THash
    _ -> fail (shows pos "Bad type in signature")
loadType (L _ [S _ "tupl", N _ n]) =
  return $  TTupl n
loadType x =
  fail (shows (annotation x) "Bad type in signature")

loadSym :: MonadFail m => SExpr Pos -> m String
loadSym (S _ sym) = return sym
loadSym x =
  fail (shows (annotation x) "Bad symbol in signature")
