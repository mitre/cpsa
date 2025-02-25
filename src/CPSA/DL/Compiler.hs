module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Simplifier (hasEpsilon)
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
compileForm k g (Diamond _ act f) =
    do
      let fvs = fv f
      let (g', k') = cloneId g k
      let (g'', fvs') = cloneIds g' fvs
      let (g''', sym) = predSym g''
      (g'''', bo, clso) <- compileAct k fvs k' fvs' g''' act
      (g'''', bk, clsk) <- compileForm k g'''' f
      return (g'''', Conj [bo, PAtm (sym, Var k' : map Var fvs')], clso ++ Clause ((sym, Var k : map Var fvs), [bk]) : clsk)

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

-- The parameters in order are:
--   the source skeleton
--   the source free vars (fvs)
--   the target skeleton
--   the target fvs
--   the generator
--   the action itself
compileAct :: MonadFail m => Id -> [Id] -> Id -> [Id] -> Gen -> Act ->
              m (Gen, Body, [Clause])
compileAct k fvs k' fvs' g (AAtom _ rel ts) =
  let (g', o) = freshId g "O" Step in
  let twas = compileTwas o fvs fvs' in
  return (g', Conj (
      PAtm ("step", [Var k, Var o, Var k']) :
      PAtm (rel, Var o:ts) :
      twas)
  , [])
compileAct k fvs k' fvs' g (ANot _ a) =
  do
    (g', b, cs) <- compileAct k fvs k' fvs' g a
    return (g', PNot b, cs)
compileAct k fvs k' fvs' g (AAnd _ as) =
  do
    (g', bs, cls) <- compileActs k fvs k' fvs' g as
    return (g', Conj bs, cls)
compileAct k fvs k' fvs' g (AOr _ as) =
  do
    (g', bs, cls) <- compileActs k fvs k' fvs' g as
    return (g', Disj bs, cls)
compileAct k fvs k' fvs' g (AExists _ xs a) =
  do
    let (g', xs') = cloneIds g xs
    (g'', bs, cls) <- compileAct k (fvs++xs) k' (fvs'++xs') g' a
    return (g'', Conj (map (genCondAtom k) xs++[bs]), cls)
compileAct k fvs k' fvs' g (ATest _ f) =
  do
    (g', bf, clsf) <- compileForm k g f
    return (g', Conj (
        bf:
        PAtm ("eq", [Var k, Var k, Var k']):
        zipWith (\a b -> PAtm ("eq", [Var k, Var a, Var b])) fvs fvs'),
      clsf)
compileAct k fvs k' fvs' g (One _) =
  do
    let (g', o) = freshId g "O" Step
    let twas = compileTwas o fvs fvs'
    return (g', Conj (
      PAtm ("step", [Var k, Var o, Var k']) : twas), [])
compileAct k fvs k' fvs' g (Concat _ []) = return (g, Conj (
                                PAtm ("eq", [Var k, Var k, Var k']):
                                zipWith (\a b -> PAtm ("eq", [Var k, Var a, Var b])) fvs fvs'), [])
compileAct k fvs k' fvs' g (Concat _ [a]) = compileAct k fvs k' fvs' g a
compileAct k fvs k' fvs' g (Concat _ as) =
  do
    let l = length as
    let (g', syms) = predSyms g l
    (g'', bs, clss) <- compileActs k fvs k' fvs' g' as
    let (g''', kfvs) = clonedKVars g'' (l-1)
    -- skeleton free variables pairs
    let kfvsprs = pairs ((k,fvs):kfvs++[(k',fvs')])
    let b = Conj (zipWith (\sym ((k'',fv''),(k''',fv'''))-> PAtm (sym, map Var (k'':fv''++k''':fv'''))) syms kfvsprs)
    let cls = zipWith (\sym b -> Clause ((sym, map Var ((k:fvs)++(k':fvs'))), [b])) syms bs ++ clss
    return (g''', b, cls)
  where
    pairs xs = zip xs (tail xs)
    clonedKVars g 0 = (g, [])
    clonedKVars g n = 
      let (g', k'') = cloneId g k in
      let (g'', fvs'') = cloneIds g' fvs in
      let (g''', xs) = clonedKVars g'' (n-1) in 
        (g''', (k'', fvs''):xs)
compileAct k fvs k'' fvs'' g (Star _ a) =
  do
    let (g', ipred) = predSym g
    let (g'', k') = cloneId g' k
    let (g''', fvs') = cloneIds g'' fvs
    (g'''', b, cls) <- compileAct k fvs k' fvs' g''' a
    return (g'''', PAtm (ipred, Var k : map Var fvs ++ Var k'' : map Var fvs''),
      Clause ((ipred, Var k : map Var fvs ++ Var k : map Var fvs), []) :
      Clause ((ipred, Var k : map Var fvs ++ Var k'' : map Var fvs''),
        b :
        [PAtm ("dif", [Var k, Var k']) | hasEpsilon a] ++
        [PAtm (ipred, Var k' : map Var fvs' ++ Var k'' : map Var fvs'')]) :
      cls)

compileActs :: MonadFail m => Id -> [Id] -> Id -> [Id] -> Gen -> [Act] ->
              m (Gen, [Body], [Clause])
compileActs _ _ _ _ g [] = return (g, [], [])
compileActs k fvs k' fvs' g (a:as) =
  do
    (g', b, cls) <- compileAct k fvs k' fvs' g a
    (g'', bs, cls') <- compileActs k fvs k' fvs' g' as
    return (g'', b:bs, cls++cls')


-- Generate a clause from some free variables and a body.
makeClause :: Id -> Gen -> [Id] -> Body -> (Gen, String, Clause)
makeClause k g vs body =
    (g', sym, Clause ((sym, map Var (k : vs)), [body]))
    where
      (g', sym) = predSym g

-- the first argument is the step, the next two are the variable lists
-- uncopied variables must be identical
compileTwas :: Id -> [Id] -> [Id] -> [Body]
compileTwas o = zipWith (\a b -> if shouldCopy (idSort a)
  then PAtm (twa (idSort a), [Var a, Var o, Var b])
  else PAtm ("eq", [Var o, Var a, Var b]))


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
genCondAtom k v@(Id (_,_,Strd)) = PAtm ("strand", [Var k, Var v])
genCondAtom k v@(Id (_,_,Role)) = PAtm ("hasRole", [Var k, Var v])
genCondAtom k v@(Id (_,_,Node)) = PAtm ("isNode", [Var k, Var v])
genCondAtom _ (Id (_,_,Mesg)) = PAtm ("true", [])
genCondAtom _ (Id (_,_,Othr)) = PAtm ("true", [])
genCondAtom _ (Id (_,sym,_)) = error ("Bad quantification sort for " ++ sym)