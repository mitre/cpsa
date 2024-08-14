module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Prolog

compileQuery :: MonadFail m => Gen -> Query -> m (Gen, [Clause])
compileQuery g (Query sym ids f) =
    do
      (g', pl) <- compileForm g f
      return (g', [Clause ((sym, map Var ids), [pl])])

compileForm :: MonadFail m => Gen -> Formula -> m (Gen, Body)
compileForm g (Atom _ sym ts) =
    return (g, PAtm (sym, ts))
compileForm g (Not _ f) =
    do
      (g', b) <- compileForm g f
      return (g', PNot b)
compileForm g (And _ fs) =
    do
      (g', bs) <- compileForms g fs
      return (g', Conj bs)
compileForm g (Or _ fs) =
    do
      (g', bs) <- compileForms g fs
      return (g', Disj bs)
compileForm g (Exists _  _ f) =
    compileForm g f
compileForm _ (Diamond _ _ _) =
    fail "cannot handle diamond"

compileForms :: MonadFail m => Gen -> [Formula] -> m (Gen, [Body])
compileForms g [] =
    return (g, [])
compileForms g (f : fs) =
    do
      (g', b) <- compileForm g f
      (g'', bs) <- compileForms g' fs
      return (g'', b : bs)
