module CPSA.DL.Prolog (Clause (..), PAtom, Body (..), pretty) where

import CPSA.Lib.Pretty
import CPSA.DL.Structs

newtype Clause = Clause (PAtom, [Body]) deriving Show

type PAtom = (String, [Term])

data Body
    = PAtm PAtom
    | Disj [Body]
    | Conj [Body]
    | PNot Body
      deriving Show

prec :: Body -> Int
prec (PAtm _) = 0
prec (PNot _) = 900
prec (Conj _) = 1000
prec (Disj _) = 1100

pretty :: Clause -> Pretty
pretty (Clause (atom, [])) = blo 0 [prettyAtom atom, str "."]
pretty (Clause (atom, [body])) =
    grp 4 (prettyAtom atom : str " :-" : brk 1 : rest ++ [str "."])
    where
      rest = prettyBody p body
      p = prec body
pretty (Clause (atom, body)) =
    grp 4 (prettyAtom atom : str " :-" : brk 1 : rest ++ [str "."])
    where
      rest = prettyBody p (Conj body)
      p = prec (Conj body)

prettyBody :: Int -> Body -> [Pretty]
prettyBody p b | p < prec b =
                   [grp 1 (str "(" : prettyBody p' b ++ [str ")"])]
                   where p' = prec b
prettyBody _ (PAtm atom) = [prettyAtom atom]
prettyBody p (Disj [b]) =
    prettyBody p b
prettyBody _ bod@(Disj (b : bs)) =
    prettyBody p b ++ prettyRest ";" p bs
    where p = prec bod
prettyBody p (Conj [b]) =
    prettyBody p b
prettyBody _ bod@(Conj (b : bs)) =
    prettyBody p b ++ prettyRest "," p bs
    where p = prec bod
prettyBody _ bod@(PNot b) =
    [grp 2 (str "\\+" : prettyBody p b)]
    where p = prec bod
prettyBody _ _ = error "Bad prolog"

prettyRest :: String -> Int -> [Body] -> [Pretty]
prettyRest _ _ [] = []
prettyRest op p (b : bs) =
    str op : brk 1 : prettyBody p b ++ prettyRest op p bs

prettyAtom :: PAtom -> Pretty
prettyAtom (pred, []) = str pred
prettyAtom (pred, arg : args) =
    blo 0 (str pred : str "(" : prettyTerm arg : prettyTerms args)

prettyTerms :: [Term] -> [Pretty]
prettyTerms [] = [str ")"]
prettyTerms (t : ts) =
    str ", " : prettyTerm t : prettyTerms ts

prettyTerm :: Term -> Pretty
prettyTerm (Var id) = str (idName id ++ "_" ++ show (idInt id))
prettyTerm (Const c) =
    blo 0 [str "\"", str c, str "\""]
prettyTerm (Num n) =
    str (show n)
prettyTerm (Pair s i) =
    blo 0 [str "[", str (show s), str ", ", str (show i), str "]"]
