module CPSA.DL.Loader (loadQuery) where

-- import Control.Monad
import Data.Char (toUpper)
import Data.List (nub, (\\))
import CPSA.Lib.SExpr
-- import CPSA.Lib.Utilities
import CPSA.DL.Structs

type Env = [(String, Id)]

loadQuery :: MonadFail m => Gen -> SExpr Pos -> m (Gen, Query)
loadQuery g (L _ (S _ "defquery" :
                  L _ (S _ name : decls) :
                  x : xs)) =
    do
      (g', env) <- loadDecls g decls
      (g'', body) <- loadForms g' env (x : xs)
      let free = nub (concat (map fv body))
      let name' = map toUnderScore name
      return (g'', Query name' (map snd env) (And free body))
loadQuery _ x =
    fail (shows (annotation x) " Malformed query")

loadDecls :: MonadFail m => Gen -> [SExpr Pos] -> m (Gen, Env)
loadDecls g [] =
    return (g, [])
loadDecls g (d : ds) =
    do
      (g', id) <- loadDecl g d
      (g'', e) <- loadDecls g' ds
      return (g'', (idName id, id) : e)

loadDecl :: MonadFail m => Gen -> SExpr Pos -> m (Gen, Id)
loadDecl g (L _ [S _ name, sort]) =
    do
      srt <- loadSort sort
      return $ freshId g (toPVar name) srt
loadDecl _ x =
    fail (shows (annotation x) " Malformed sort")

loadSort :: MonadFail m => SExpr Pos -> m Sort
loadSort (S _ "mesg") = return Mesg
loadSort (S _ "strd") = return Strd
loadSort (S _ "role") = return Role
loadSort (S _ "node") = return Node
loadSort (S _ "indx") = return Indx
loadSort (S _ "othr") = return Othr
loadSort x = fail (shows (annotation x) " Bad sort: ")

loadForm :: MonadFail m => Gen -> Env -> SExpr Pos -> m (Gen, Formula)
loadForm g env (L _ [S _ "not", x]) =
    do
      (g', f) <- loadForm g env x
      return (g', Not (fv f) f)
loadForm g env (L _ (S _ "and" : xs)) =
    do
      (g', fs) <- loadForms g env (xs)
      return (g', And (nub (concat (map fv fs))) fs)
loadForm g env (L _ (S _ "or" : x : xs)) =
    do
      (g', fs) <- loadForms g env (x : xs)
      return (g', Or (nub (concat (map fv fs))) fs)
loadForm g env (S pos "top") =
    loadForm g env (L pos [S pos "and"])
loadForm g env (L _ [S _ "exists", L _ decls, x]) =
    do
      (g', env') <- loadDecls g decls
      (g'', f) <- loadForm g' (env' ++ env) x
      let ids = map snd env'
      return (g'', Exists (fv f \\ ids) ids f)
loadForm g env (L _ [S _ "diamond", act, x]) =
    do
      (g', f) <- loadForm g env x
      let fvs = fv f
      (g'', a) <- loadAct g' env fvs act
      return (g'', Diamond fvs a f)
-- Derived forms
loadForm g env (L pos [S _ "forall", decls, x]) =
    loadForm g env (L pos [S pos "not",
                           L pos [S pos "exists", decls,
                                  L pos [S pos "not", x]]])
loadForm g env (L pos [S _ "box", act, x]) =
    loadForm g env (L pos [S pos "not",
                           L pos [S pos "diamond", act,
                                  L pos [S pos "not", x]]])
-- Atoms
loadForm g env (L _ (S _ sym : xs)) =
    do
      ts <- loadTerms env xs
      let free = getFree ts
      return (g, Atom free (map toUnderScore sym) ts)
loadForm _ _ x =
    fail (shows (annotation x) " Malformed formula")

loadForms :: MonadFail m => Gen -> Env -> [SExpr Pos] -> m (Gen, [Formula])
loadForms g _ [] =
    return (g, [])
loadForms g env (x : xs) =
    do
      (g', f) <- loadForm g env x
      (g'', fs) <- loadForms g' env xs
      return (g'', f : fs)

loadAct :: MonadFail m => Gen -> Env -> [Id] -> SExpr Pos -> m (Gen, Act)
loadAct g env fv (L _ [S _ "not", act]) =
    do
        (g', a) <- loadAct g env fv act
        return (g', ANot (fva a) a)
loadAct g env fv (L _ ((S _ "and"):acts)) =
    do
      (g', fs) <- loadActs g env fv acts
      return (g', AAnd (nub (fv ++ concatMap fva fs)) fs)
loadAct g env fv (L _ ((S _ "or"):acts)) =
    do
      (g', fs) <- loadActs g env fv acts
      return (g', AOr (nub (fv ++ concatMap fva fs)) fs)
loadAct g env fv (L _ [S _ "exists", L _ decls, act]) =
    do
      (g', env') <- loadDecls g decls
      (g'', a) <- loadAct g' (env' ++ env) fv act
      let ids = map snd env'
      return (g'', AExists (fva a \\ ids) ids a)
loadAct g env fv (L pos [S _ "forall", decls, x]) =
    loadAct g env fv (L pos [S pos "not",
                           L pos [S pos "exists", decls,
                                  L pos [S pos "not", x]]])
loadAct g _ fv (S _ "one") = return (g, One fv)
loadAct g env fv (S pos "epsilon") =
    loadAct g env fv (L pos [S pos "concat"]) -- empty concat is epsilon
loadAct g env fv (L _ ((S _ "concat"):acts)) =
    do
      (g', fs) <- loadActs g env fv acts
      return (g', Concat (nub (fv ++ concatMap fva fs)) fs)
loadAct g env fv (L pos [S _ "plus", act]) =
    loadAct g env fv (L pos [S pos "concat", act, L pos [S pos "star", act]])
loadAct g env fv (L _ [S _ "star", act]) =
    do
        (g', a) <- loadAct g env fv act
        return (g', Star (fva a) a)
-- Atoms
loadAct g env fv (L _ (S _ sym : xs)) =
    do
      ts <- loadTerms env xs
      let free = fv ++ getFree ts
      return (g, AAtom free (map toUnderScore sym) ts)
loadAct _ _ _ act =
    fail (shows (annotation act) " Bad action")

loadActs :: MonadFail m => Gen -> Env -> [Id] -> [SExpr Pos] -> m (Gen, [Act])
loadActs g _ _ [] = return (g, [])
loadActs g env fv (act:acts) =
    do
        (g', a) <- loadAct g env fv act
        (g'', as) <- loadActs g' env fv acts
        return (g'', a:as)

loadTerms :: MonadFail m => Env -> [SExpr Pos] -> m [Term]
loadTerms e xs = mapM (loadTerm e) xs

loadTerm :: MonadFail m => Env -> SExpr Pos -> m Term
loadTerm e (S pos name) =
    case lookup (toPVar name) e of
      Just id ->
          return $ Var id
      Nothing ->
          fail (shows pos (" Variable " ++ name ++ " not declared"))
loadTerm _ (Q _ str) =
    return $ Const str
loadTerm _ (N _ num) =
    return $ Num num
loadTerm _ (L _ [N _ s, N _ i]) =
    return $ Pair s i
loadTerm _ x =
    fail (shows (annotation x) " Malformed term")

getFree :: [Term] -> [Id]
getFree [] = []
getFree (Var id : ts) =
    id : getFree ts
getFree (_ : ts) =
    getFree ts

toPVar :: String -> String
toPVar (c : s) = map toUnderScore $ toUpper c : s
toPVar [] = []

toUnderScore :: Char -> Char
toUnderScore '-' = '_'
toUnderScore c = c
