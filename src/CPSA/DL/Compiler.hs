module CPSA.DL.Compiler where

import CPSA.DL.Structs
import CPSA.DL.Prolog
import Data.Maybe (mapMaybe)

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
compileForm k g (Diamond vs act f) =
    do
      (g', b, cls) <- compileForm k g f
      let (g'', sym') = predSym g'
      let (g''', sym, cl) = makeClause k g'' vs b
      let (g'''', connCl) = connectByAct g''' act sym sym' k vs
      return (g'''', PAtm (sym', map Var (k : vs)), cl : cls ++ connCl)

connectByAct :: Gen -> Act -> String -> String -> Id -> [Id] -> (Gen, [Clause])
-- Atomic jumps
connectByAct g (AAtom sym ts) pred1 pred2 k fv =
    let (g', k') = cloneId g k
        (g'', fvm) = cloneVars g' fv -- "free variable map"
        (g''', s) = freshId g'' "O" Othr -- step variable
        fv' = map snd fvm in
    (g''', [Clause ((pred2, map Var (k':fv')) , [Conj (
      PAtm ("step", map Var [k',s,k]) : -- NOTE: this is necessary
      PAtm (pred1, map Var (k:fv)) :
      PAtm (sym, Var s: ts) :
      mapMaybe (twaPred s) fvm
    )])])

-- \epsilon jumps
connectByAct g (Cat []) pred1 pred2 k fv =
    let vs = map Var (k:fv) in
      (g, [Clause ((pred2, vs) , [PAtm (pred1, vs)])])
-- Concatination makes new preds
connectByAct g (Cat [act]) pred1 pred2 k fv = connectByAct g act pred1 pred2 k fv
connectByAct g (Cat (a:as)) pred1 pred2 k fv =
    let (g', pred3) = predSym g
        (g'', cl) = connectByAct g' a pred1 pred3 k fv
        (g''', cl') = connectByAct g'' (Cat as) pred3 pred2 k fv in
    (g''', cl ++ cl')
-- no jump
connectByAct g (Cup []) _ _ _ _ = (g, [])
-- union adds all possible connections
connectByAct g (Cup (a:as)) pred1 pred2 k fv =
  let (g', cl) = connectByAct g a pred1 pred2 k fv
      (g'', cl') = connectByAct g' (Cup as) pred1 pred2 k fv in
  (g'', cl ++ cl')
-- star adds a self-connection and an epsilon jump
connectByAct g (Star act) pred1 pred2 k fv =
  let (g', cl) = connectByAct g act pred1 pred1 k fv
      (g'', cl') = connectByAct g' (Cat []) pred1 pred2 k fv in
  (g'', cl ++ cl')

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

-- compileStep :: Id -> Gen -> [Clause] -> Act ->
--                String -> [Id] -> (Gen, Body, [Clause])
-- compileStep k g cls act sym vs =
--     (g'', Conj (step act : twas), cls)
--     where
--       (g', k') = cloneId g k
--       (g'', tvs) = cloneVars g' vs
--       step act =
--           PAtm ("step" ++ actSuffix act, [Var k, Sym "O", Var k'])
--       twas = compileTwas act k k' tvs
--              [PAtm (sym, Var k' : map (Var . snd) tvs)]

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
      Othr -> (g, v) -- Don't clone integers


-- step -> var pair -> twa pred
twaPred :: Id -> (Id,Id) -> Maybe Body
twaPred s (v,v') =  case idSort v of
  Othr -> Nothing
  _ -> Just (PAtm (twa $ idSort v, map Var [v, s, v']))

twa :: Sort -> String
twa Mesg = "mtwa"
twa Strd = "stwa"
twa Node = "ntwa"
twa Othr = error "Bad TWA sort"

