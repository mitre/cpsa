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
      let (g', k') = freshId g "k" Skel
      (g', b, cls) <- compileForm k' g f
      let vs = fv f
      let (g'', sym, cl) = makeClause k g' vs b
      return 

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
  let (g', o) = freshId g "o" Step in
  (g, Conj [
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
compileAct k k' g (AExists _ _ a) =
  compileAct k k' g a
compileAct k k' g (Concat _ as) =
  let (g', bs, cls) = compileConcat k k' g as in
    (g', Conj bs, cls)
compileAct k k' g (Star fvs a) =
  let (g', sym) = predSym g in
  let (g'', ik) = freshId g' "k" Skel in -- internal skeleton
  let (g''', ik') = freshId g'' "k" Skel in
  let (g'''', ik'') = freshId g''' "k" Skel in
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
compileConcat k k'' g (a:as) =
  let (g', k') = freshId g "k" Skel in
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
      Othr -> (g, v) -- Don't clone integers

compileTwas :: Act -> Id -> Id -> [(Id, Id)] -> [Body] -> [Body]
compileTwas _ _ _ [] bs = bs
compileTwas act k k' ((v, v') : tvs) bs =
    case idSort v of
      Othr -> bs'
      _ -> twaAtom act k v k' v' : bs'
    where
      bs' = compileTwas act k k' tvs bs

twa :: Sort -> String
twa Mesg = "mtwa"
twa Strd = "stwa"
twa Node = "ntwa"
twa _ = error "Bad TWA sort"
