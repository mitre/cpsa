module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Prolog

compileQuery :: MonadFail m => Id -> Gen -> Query -> m (Gen, [Clause])
compileQuery k g (Query sym ids f) =
    do
      (g', pl, cls) <- compileForm k g f
      return (g', Clause ((sym, map Var (k : ids)), map (genCondAtom k) (k:ids)++[pl]) : cls)

compileForm :: MonadFail m => Id -> Gen -> Formula ->
               m (Gen, Body, [Clause])
compileForm k g (Atom _ sym ts) =
    return (g, PAtm (sym, Var k : ts), [])
compileForm k g (Not _ f) =
    do
      (g', b, cls) <- compileForm k g f
      return (g', PNot b, cls)
compileForm _ g (And _ []) =
  return (g, PAtm ("true", []), [])
compileForm k g (And _ fs) =
    do
      (g', bs, cls) <- compileForms k g fs
      return (g', Conj bs, cls)
compileForm k g (Or _ fs) =
    do
      (g', bs, cls) <- compileForms k g fs
      return (g', Disj bs, cls)
compileForm k g (Exists _  xs f) =
    do
      (g', b, cls) <- compileForm k g f
      return (g', Conj (map (genCondAtom k) xs++[b]), cls)
compileForm k g (Diamond fvs act f) =
    do
      let (g', sym) = predSym g
      let (g'', bo, clso) = compileAct k (sym, length fvs) g' act
      (g''', bk, clsk) <- compileForm k g'' f
      return (g''', bo , clso++(Clause ((sym, map Var (k:fvs)), [bk]):clsk))

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

-- the second argument is the predicate symbol
-- and the number of non-skel arguments
compileAct :: Id -> (String, Int) -> Gen -> Act -> 
              (Gen, Body, [Clause])
compileAct k (pred, n) g (AAtom fvs rel ts) =
  let (g', k') = freshId g "K" Skel in
  let (g'', o) = freshId g' "O" Step in
  let (g''', fvs', twaBs) = compileTwas g'' o (take n fvs) in
  (g''', Conj ([
    PAtm ("step", [Var k, Var o, Var k']),
    PAtm (rel, Var o:ts)
  ] ++ twaBs ++
  [
      PAtm (pred, map Var (k:take n fvs'))
  ]), [])
compileAct k d g (ANot _ a) =
  let (g', b, cs) = compileAct k d g a in
  (g', PNot b, cs)
compileAct k d g (AAnd _ as) =
  let (g', bs, cls) = compileActs k d g as in
    (g', Conj bs, cls)
compileAct k d g (AOr _ as) =
  let (g', bs, cls) = compileActs k d g as in
    (g', Disj bs, cls)
compileAct k d g (AExists _ xs a) =
  let (g', bs, cls) = compileAct k d g a in
    (g', Conj (map (genCondAtom k) xs++[bs]), cls)
compileAct k (pred,n) g (One fvs) = 
  let (g', k') = freshId g "K" Skel in
  let (g'', o) = freshId g' "O" Step in
  let (g''', fvs', twaBs) = compileTwas g'' o (take n fvs) in
  (g''', Conj ([
    PAtm ("step", [Var k, Var o, Var k'])
  ] ++ twaBs ++
  [
      PAtm (pred, map Var (k:take n fvs'))
  ]), [])
compileAct k (pred,n) g (Concat fvs []) = (g, PAtm (pred, map Var (k:take n fvs)), [])
compileAct k d g (Concat _ [a]) = compileAct k d g a
compileAct k d g (Concat fvs (a:as)) =
  let (g', sym) = predSym g in
  let (g'', b, cls) = compileAct k (sym, length fvs) g' a in
  let (g''', b', cls') = compileAct k d g'' (Concat fvs as) in
    (g''', b, Clause ((sym, map Var (k:fvs)), [b']):cls++cls')
compileAct k (dpred, n) g (Star fvs a) =
  let (g', ipred) = predSym g in
  let (g'', k') = freshId g' "K" Skel in
  let (g''', b, cls) = compileAct k' (ipred,n) g'' a in
  let iatm = (ipred, map Var (k:take n fvs)) in
    (g''', PAtm iatm,
      Clause (iatm, [b]) :
      Clause (iatm, [PAtm (dpred, map Var (k:take n fvs))]) :
      cls
    )

compileActs :: Id -> (String, Int) -> Gen -> [Act] -> 
              (Gen, [Body], [Clause])
compileActs _ _ g [] = (g, [], [])
compileActs k d g (a:as) =
  let (g', b, cls) = compileAct k d g a in
  let (g'', bs, cls') = compileActs k d g' as in
    (g'', b:bs, cls++cls')


-- Generate a clause from some free variables and a body.
makeClause :: Id -> Gen -> [Id] -> Body -> (Gen, String, Clause)
makeClause k g vs body =
    (g', sym, Clause ((sym, map Var (k : vs)), [body]))
    where
      (g', sym) = predSym g

-- copies the variables and includes all the TWA relations
-- the second argument is a Prolog variable for the operation
compileTwas :: Gen -> Id -> [Id] -> (Gen, [Id], [Body])
compileTwas g _ [] = (g, [], [])
compileTwas g o (v : vs) =
  let (g', vs', bs) = compileTwas g o vs in
  if shouldCopy (idSort v)
    then 
      let (g'', v') = cloneId g v in
        (g'', v':vs', PAtm (twa (idSort v), [Var v, Var o, Var v']):bs)
    else (g', v:vs', bs)


shouldCopy :: Sort -> Bool
shouldCopy Skel = True
shouldCopy Step = True
shouldCopy Mesg = True
shouldCopy Strd = True
shouldCopy Node = True
shouldCopy Indx = False
shouldCopy Role = False
shouldCopy Othr = False


twa :: Sort -> String
twa Mesg = "mtwa"
twa Strd = "stwa"
twa Node = "ntwa"
twa _ = error "Bad TWA sort"

genCondAtom :: Id -> Id -> Body
genCondAtom _ k@(Id (_,_,Skel)) = PAtm ("skel", [Var k])
genCondAtom k v@(Id (_,_,Strd)) = PAtm ("pl", [Var k, UScore, Var v, UScore])
genCondAtom k v@(Id (_,_,Role)) = PAtm ("hasRole", [Var k, Var v])
genCondAtom _ (Id (_,_,Mesg)) = PAtm ("true", [])
genCondAtom _ (Id (_,sym,_)) = error ("Bad quantification sort for " ++ sym)