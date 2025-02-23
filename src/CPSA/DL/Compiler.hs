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
      let (g'''', bo, clso) = compileAct k fvs k' fvs' g''' act
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
compileAct :: Id -> [Id] -> Id -> [Id] -> Gen -> Act ->
              (Gen, Body, [Clause])
compileAct k fvs k' fvs' g (AAtom _ rel ts) =
  let (g', o) = freshId g "O" Step in
  let twas = compileTwas o fvs fvs' in
  (g', Conj (
      PAtm ("step", [Var k, Var o, Var k']) :
      PAtm (rel, Var o:ts) :
      twas)
  , [])
compileAct k fvs k' fvs' g (ANot _ a) =
  let (g', b, cs) = compileAct k fvs k' fvs' g a in
  (g', PNot b, cs)
compileAct k fvs k' fvs' g (AAnd _ as) =
  let (g', bs, cls) = compileActs k fvs k' fvs' g as in
    (g', Conj bs, cls)
compileAct k fvs k' fvs' g (AOr _ as) =
  let (g', bs, cls) = compileActs k fvs k' fvs' g as in
    (g', Disj bs, cls)
compileAct k fvs k' fvs' g (AExists _ xs a) =
  let (g', xs') = cloneIds g xs in
  let (g'', bs, cls) = compileAct k (fvs++xs) k' (fvs'++xs') g' a in
    (g'', Conj (map (genCondAtom k) xs++[bs]), cls)
compileAct k fvs k' fvs' g (One _) =
  let (g', o) = freshId g "O" Step in
  let twas = compileTwas o fvs fvs' in
  (g', Conj (
    PAtm ("step", [Var k, Var o, Var k']) : twas)
  , [])
compileAct k fvs k' fvs' g (Concat _ []) = (g, Conj (
                                PAtm ("eq", [Var k, Var k, Var k']):
                                zipWith (\a b -> PAtm ("eq", [Var k, Var a, Var b])) fvs fvs'
                              ), [])
compileAct k fvs k' fvs' g (Concat _ [a]) = compileAct k fvs k' fvs' g a
compileAct k fvs k' fvs' g (Concat _ as) =
  let l = length as in
  let (g', syms) = predSyms g l in
  let (g'', bs, clss) = compileActs k fvs k' fvs' g' as in
  let (g''', kfvs) = clonedKVars g'' (l-1) in
  -- skeleton free variables pairs
  let kfvsprs = pairs ((k,fvs):kfvs++[(k',fvs')]) in
  let b = Conj (zipWith (\sym ((k'',fv''),(k''',fv'''))-> PAtm (sym, map Var (k'':fv''++k''':fv'''))) syms kfvsprs) in
  let cls = zipWith (\sym b -> Clause ((sym, map Var ((k:fvs)++(k':fvs'))), [b])) syms bs ++ clss in
    (g''', b, cls)
  where
    pairs xs = zip xs (tail xs)
    clonedKVars g 0 = (g, [])
    clonedKVars g n = 
      let (g', k'') = cloneId g k in
      let (g'', fvs'') = cloneIds g' fvs in
      let (g''', xs) = clonedKVars g'' (n-1) in 
        (g''', (k'', fvs''):xs)
compileAct k fvs k'' fvs'' g (Star _ a) =
  let (g', ipred) = predSym g in
  let (g'', k') = cloneId g' k in
  let (g''', fvs') = cloneIds g'' fvs in
  let (g'''', b, cls) = compileAct k fvs k' fvs' g''' a in
    (g'''', PAtm (ipred, Var k : map Var fvs ++ Var k'' : map Var fvs''),
      Clause ((ipred, Var k : map Var fvs ++ Var k : map Var fvs), []) :
      Clause ((ipred, Var k : map Var fvs ++ Var k'' : map Var fvs''),
        b :
        [PAtm ("dif", [Var k, Var k']) | hasEpsilon a] ++
        [PAtm (ipred, Var k' : map Var fvs' ++ Var k'' : map Var fvs'')]) :
      cls
    )

compileActs :: Id -> [Id] -> Id -> [Id] -> Gen -> [Act] ->
              (Gen, [Body], [Clause])
compileActs _ _ _ _ g [] = (g, [], [])
compileActs k fvs k' fvs' g (a:as) =
  let (g', b, cls) = compileAct k fvs k' fvs' g a in
  let (g'', bs, cls') = compileActs k fvs k' fvs' g' as in
    (g'', b:bs, cls++cls')


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