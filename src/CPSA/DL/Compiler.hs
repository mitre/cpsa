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
compileForm k g (And _ []) =
  return (g, PAtm ("skel", [Var k]), [])
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
compileForm k g (Diamond _ act f) =
    do
      let (g', k') = freshId g "K" Skel
      (g'', b, cls) <- compileForm k' g' f
      let (g''', b', cls') = compileAct k k' g'' act
      return (g''', Conj [b', b] , cls'++cls)

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

compileAct :: Id -> Id -> Gen -> Act -> 
              (Gen, Body, [Clause])
compileAct k k' g (AAtom _ sym ts) =
  let (g', o) = freshId g "O" Step in
  (g', Conj [
    PAtm ("step", [Var k, Var o, Var k']),
    PAtm (sym, Var o:ts)
  ], [])
compileAct k k' g (ANot _ a) =
  let (g', b, cs) = compileAct k k' g a in
  (g', PNot b, cs)
compileAct k k' g (AAnd _ as) =
  let (g', bs, cls) = compileActs k k' g as in
    (g', Conj bs, cls)
compileAct k k' g (AOr _ as) =
  let (g', bs, cls) = compileActs k k' g as in
    (g', Disj bs, cls)
compileAct k k' g (AExists _ xs a) =
  let (g', bs, cls) = compileAct k k' g a in
    (g', Conj (map (genCondAtom k) xs++[bs]), cls)
compileAct k k' g One =
  (g, PAtm ("step", [Var k, UScore, Var k']), [])
compileAct k k' g (Concat _ as) =
  let (g', bs, cls) = compileConcat k k' g as in
    (g', Conj bs, cls)
compileAct k k' g (Star fvs a) =
  let (g', sym) = predSym g in
  let (g'', ik) = freshId g' "K" Skel in -- internal skeleton
  let (g''', ik') = freshId g'' "K" Skel in
  let (g'''', ik'') = freshId g''' "K" Skel in
  let (g''''', b, cls) = compileAct ik ik' g'''' a in
  let pred from to = (sym, map Var (from:to:fvs)) in
    (g''''', PAtm (pred k k'),
      Clause (pred ik ik'', [b, PAtm (pred ik' ik'')]) :
      Clause (pred ik ik, []) :
      cls
    )

compileActs :: Id -> Id -> Gen -> [Act] -> 
              (Gen, [Body], [Clause])
compileActs _ _ g [] = (g, [], [])
compileActs k k' g (a:as) =
  let (g', b, cls) = compileAct k k' g a in
  let (g'', bs, cls') = compileActs k k' g' as in
    (g'', b:bs, cls++cls')

compileConcat :: Id -> Id -> Gen -> [Act] ->
                  (Gen, [Body], [Clause])
compileConcat _ _ g [] = (g, [], [])
compileConcat k k' g [a] =
  let (g', b, cls) = compileAct k k' g a in
    (g', [b], cls)
compileConcat k k'' g (a:as) =
  let (g', k') = freshId g "K" Skel in
  let (g'', b, cls) = compileAct k k' g' a in
  let (g''', bs, cls') = compileConcat k' k'' g'' as in
  (g''', b:bs, cls++cls')

-- Generate a clause from some free variables and a body.
makeClause :: Id -> Gen -> [Id] -> Body -> (Gen, String, Clause)
makeClause k g vs body =
    (g', sym, Clause ((sym, map Var (k : vs)), [body]))
    where
      (g', sym) = predSym g

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
      Skel -> cloneId g v
      Step -> cloneId g v
      Mesg -> cloneId g v
      Strd -> cloneId g v
      Node -> cloneId g v
      Indx -> (g, v) -- Don't clone integers
      Role -> (g, v) -- quoted tag, so never changes
      Othr -> (g, v)

compileTwas :: Act -> Id -> Id -> [(Id, Id)] -> [Body] -> [Body]
compileTwas _ _ _ [] bs = bs
compileTwas act k k' ((v, v') : tvs) bs =
    case idSort v of
      Othr -> bs'
      _ -> twaAtom k v k' v' : bs'
    where
      bs' = compileTwas act k k' tvs bs

twaAtom :: Id -> Id -> Id -> Id -> Body
twaAtom k v k' v' =
  PAtm (twa (idSort v),
            [Var k, Var v, Var k', Var v'])



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