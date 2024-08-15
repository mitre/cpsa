module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Prolog

compileQuery :: MonadFail m => Id -> Gen -> Query -> m (Gen, [Clause])
compileQuery k g (Query sym ids f) =
    do
      (g', pl) <- compileForm k g f
      return (g', [Clause ((sym, map Var (k : ids)), [pl])])

compileForm :: MonadFail m => Id -> Gen -> Formula -> m (Gen, Body)
compileForm k g (Atom _ sym ts) =
    return (g, PAtm (sym, (Var k : ts)))
compileForm k g (Not _ f) =
    do
      (g', b) <- compileForm k g f
      return (g', PNot b)
compileForm k g (And _ fs) =
    do
      (g', bs) <- compileForms k g fs
      return (g', Conj bs)
compileForm k g (Or _ fs) =
    do
      (g', bs) <- compileForms k g fs
      return (g', Disj bs)
compileForm k g (Exists _  _ f) =
    compileForm k g f
compileForm _ _ (Diamond _ _ _) =
    fail "cannot handle diamond"

compileForms :: MonadFail m => Id -> Gen -> [Formula] -> m (Gen, [Body])
compileForms _ g [] =
    return (g, [])
compileForms k g (f : fs) =
    do
      (g', b) <- compileForm k g f
      (g'', bs) <- compileForms k g' fs
      return (g'', b : bs)
