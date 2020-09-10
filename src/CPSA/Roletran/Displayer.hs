-- Displays protocols and terms as S-expressions

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Roletran.Displayer (
  displayProt, displayTerm, displaySort) where

import qualified Data.List as L
import qualified Data.Map.Strict as M
import CPSA.Lib.SExpr
import CPSA.Roletran.Algebra
import CPSA.Roletran.Protocol

-- Display of protocols

displayProt :: Prot -> SExpr ()
displayProt p =
  L () (S () "defprotocol" : S () (pname p) : S () "basic" : rs)
  where
    rs = map displayRole (roles p)

-- Display of roles

displayRole :: Role -> SExpr ()
displayRole r =
  L () (S () "defrole" :
        S () (rname r) :
        L () (S () "vars" : displayVars (rvars r)) :
        L () (S () "trace" : displayTrace (rtrace r)) :
        displayOptional "uniq-orig" (map displayTerm uniques)
         (displayOptional "inputs" (map displayTerm (rinputs r))
           (displayOptional "outputs" (map displayTerm (routputs r)) [])))
  where
    uniques = L.sort (map fst (runiques r))

displayOptional :: String -> [SExpr ()] -> [SExpr ()] -> [SExpr ()]
displayOptional _ [] rest = rest
displayOptional key value rest =
  L () (S () key : value) : rest

displayVars :: VarEnv -> [SExpr ()]
displayVars env =
  case map displayVar (M.toList env) of
    [] -> []
    (v,t):pairs -> loop t [v] pairs
  where
    loop t vs [] = [L () (reverse (t:vs))]
    loop t vs ((v',t'):xs)
      | t == t' = loop t (v':vs) xs
      | otherwise = L () (reverse (t:vs)):loop t' [v'] xs
    displayVar (v, s) = (S () v, S () $ displaySort s)

displaySort :: Sort -> String
displaySort Text = "text"
displaySort Data = "data"
displaySort Name = "name"
displaySort Skey = "skey"
displaySort Akey = "akey"
displaySort Ikey = "ikey"
displaySort Mesg = "mesg"
displaySort Chan = "chan"

displayTrace :: Trace -> [SExpr ()]
displayTrace trace =
    map displayDt trace
    where
      displayDt (In _ ch t) =
        L () [S () "recv", displayTerm ch, displayTerm t]
      displayDt (Out _  ch t) =
        L () [S () "send", displayTerm ch, displayTerm t]

displayTerm :: Term -> SExpr ()
displayTerm (Txt v) = S () v
displayTerm (Dta v) = S () v
displayTerm (Nam v) = S () v
displayTerm (Sky k) = displaySkey k
displayTerm (Aky k) = displayAkey k
displayTerm (Msg v) = S () v
displayTerm (Tag v) = Q () v
displayTerm (Pr x y) =
  L () (S () "cat" : displayTerm x : displayList y)
displayTerm (En x y) =
  L () (S () "enc" : displayEnc x y)
displayTerm (Hsh x) =
  L () (S () "cat" : displayList x)
displayTerm (Chn v) = S () v

displaySkey :: Skey -> SExpr ()
displaySkey (SVar v) = S () v
displaySkey (Ltk x y) =
  L () [S () "ltk", S () x, S () y]

displayAkey :: Akey -> SExpr ()
displayAkey (AVar v) = S () v
displayAkey (Inv v) =
  L () [S () "invk", S () v]
displayAkey (Pubk v) =
  L () [S () "pubk", S () v]
displayAkey (Pubk2 c v) =
  L () [S () "pubk", Q () c, S () v]
displayAkey (Privk v) =
  L () [S () "privk", S () v]
displayAkey (Privk2 c v) =
  L () [S () "privk", Q () c, S () v]

displayList :: Term -> [SExpr ()]
displayList (Pr x y) = displayTerm x : displayList y
displayList t = [displayTerm t]

displayEnc :: Term -> Term -> [SExpr ()]
displayEnc (Pr x y) t = displayTerm x : displayEnc y t
displayEnc x y = [displayTerm x, displayTerm y]
