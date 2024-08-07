module CPSA.DL.Structs where

data Sort = Mesg | Strand | Label | Index | Node | Length deriving Show

-- Identifiers from the algebra module with sorts added

-- An identifier is a variable with its sort

newtype Id = Id (Integer, String, Sort) deriving Show

-- The integer distinguishes an identifier, the string is for printing.

instance Eq Id where
    (Id (x, _, _)) == (Id (x', _, _)) = x == x'

instance Ord Id where
    compare (Id (x, _, _)) (Id (x', _, _)) = compare x x'

idName :: Id -> String
idName (Id (_, name, _)) = name

idSort :: Id -> Sort
idSort (Id (_, _, sort)) = sort

-- Counter used for generating fresh identifiers.

newtype Gen = Gen (Integer) deriving (Show, Eq)

origin :: Gen
origin = Gen (0)

freshId :: Gen -> String -> Sort -> (Gen, Id)
freshId (Gen i) name sort = (Gen (i + 1), Id (i, name, sort))

cloneId :: Gen -> Id -> (Gen, Id)
cloneId gen x = freshId gen (idName x) (idSort x)

predSym :: Gen -> (Gen, String)
predSym (Gen i) = (Gen (i + 1), "pred" ++ show i)

-- A term is a variable or a constant.

data Term
    = Var Id
    | Const String
      deriving Show

-- Every formula begins with the set of free variables.

data Formula
    = Atom [Id] String [Term]
    | Not [Id] Formula
    | And [Id] [Formula]
    | Or [Id] [Formula]
    | Exists [Id] [Id] Formula
    | Diamond [Id] Act Formula
      deriving Show

-- Free variables

fv :: Formula -> [Id]
fv (Atom fv _ _) = fv
fv (Not fv _) = fv
fv (And fv _) = fv
fv (Or fv _) = fv
fv (Exists fv _ _) = fv
fv (Diamond fv _ _) = fv

data Act
    = One
    | Star
      deriving Show

data Query = Query String [Id] Formula
      deriving Show
