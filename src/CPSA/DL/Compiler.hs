module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Prolog

compileQuery :: MonadFail m => Id -> Gen -> Query -> m (Gen, [Clause])
compileQuery k g (Query sym ids f) =
    do
      (g', pl, cls) <- compileForm k g f
      return (g', Clause ((sym, map Var (k : ids)), [pl]) : cls)

compileForm :: MonadFail m => Id -> Gen -> Formula ->
               m (Gen, Body, [Clause])
compileForm k g (Atom _ sym ts) =
    return (g, PAtm (sym, Var k : ts), [])
compileForm k g (Not _ f) =
    do
      (g', b, cls) <- compileForm k g f
      let vs = fv f
      let (g'', sym, cl) = makeClause k g' vs b
      return (g'', PNot (PAtm (sym, map Var (k : vs))), cl : cls)
compileForm k g (And _ fs) =
    do
      (g', bs, cls) <- compileForms k g fs
      return (g', Conj bs, cls)
compileForm k g (Or _ fs) =
    do
      (g', bs, cls) <- compileForms k g fs
      return (g', Disj bs, cls)
compileForm k g (Exists _  _ f) =
    compileForm k g f
compileForm k g (Diamond _ act f) =
    do
      (g', b, cls) <- compileForm k g f
      let vs = fv f
      let (g'', sym, cl) = makeClause k g' vs b
      let suffix = case act of
                     One -> ""
                     Star -> "star"
      return $ compileStep k g'' (cl : cls) suffix sym vs

-- Compile a list of formulas.
compileForms :: MonadFail m => Id -> Gen -> [Formula] ->
                m (Gen, [Body], [Clause])
compileForms _ g [] =
    return (g, [], [])
compileForms k g (f : fs) =
    do
      (g', b, cls) <- compileForm k g f
      (g'', bs, cls') <- compileForms k g' fs
      return (g'', b : bs, cls ++ cls')

-- Generate a clause from some free variables and a body.
makeClause :: Id -> Gen -> [Id] -> Body -> (Gen, String, Clause)
makeClause k g vs body =
    (g', sym, Clause ((sym, map Var (k : vs)), [body]))
    where
      (g', sym) = predSym g

compileStep :: Id -> Gen -> [Clause] -> String ->
               String -> [Id] -> (Gen, Body, [Clause])
compileStep k g cls suffix sym vs =
    (g'', Conj (PAtm ("step", [Var k, Const "_", Var k']) : twas), cls)
    where
      (g', k') = cloneId g k
      (g'', tvs) = cloneVars g' vs
      twas = compileTwas suffix k k' tvs
             [PAtm (sym, Var k' : map (Var . snd) tvs)]

cloneVars :: Gen -> [Id] -> (Gen, [(Id, Id)])
cloneVars g [] = (g, [])
cloneVars g (v : vs) =
    (g'', (v, v') : vs')
    where
      (g', vs') = cloneVars g vs
      (g'', v') = cloneVar g' v

cloneVar :: Gen -> Id -> (Gen, Id)
cloneVar g v =
    case idSort v of
      Mesg -> cloneId g v
      Strd -> cloneId g v
      Node -> cloneId g v
      Intr -> (g, v) -- Don't clone integers

compileTwas :: String -> Id -> Id -> [(Id, Id)] -> [Body] -> [Body]
compileTwas _ _ _ [] bs = bs
compileTwas suffix k k' ((v, v') : tvs) bs =
    case idSort v of
      Mesg ->
          PAtm ("mtwa" ++ suffix, [Var k, Var v, Const "_",
                                       Var k', Var v']) : bs'
      Strd ->
          PAtm ("stwa" ++ suffix, [Var k, Var v, Const "_",
                                       Var k', Var v']) : bs'
      Node ->
          PAtm ("ntwa" ++ suffix, [Var k, Var v, Const "_",
                                       Var k', Var v']) : bs'
      Intr -> bs' -- Don't translate integers
    where
      bs' = compileTwas suffix k k' tvs bs
