module CPSA.Db.Loader (State, step) where

import Control.Monad
import qualified Data.List as L
import CPSA.Algebra
import CPSA.Lib.SExpr
import CPSA.Signature (Sig, loadSig)
import CPSA.Db.Structs
import CPSA.Channel
import CPSA.Protocol (Event (..), Trace, evtMap)

type State = ([Prot], [Skel])

step :: Sig -> String -> Gen -> State ->
        SExpr Pos -> IO State
step _ _ _  state (L _ (S _ "comment" : _)) =
     return state
step sig nom origin (ps, ks) (L pos (S _ "defprotocol" : prot)) =
    do
      prot <- loadProt sig nom origin pos prot
      return (prot : ps, ks)
step _ _ _ (ps, ks) (L pos (S _ "defskeleton" : xs)) =
    do
      k <- findSkel pos ps xs
      return (ps, k : ks)
step _ _ _  state _ =
     return state

loadProt :: MonadFail m => Sig -> String -> Gen -> Pos ->
            [SExpr Pos] -> m (Prot)
loadProt sig nom origin pos (S _ name : S _ alg : x : xs)
    | alg /= nom =
        fail (shows pos $ "Expecting terms in algebra " ++ nom)
    | otherwise =
        do
          sig <- loadLang pos sig xs
          (gen, rs) <- loadRoles sig origin (x : xs)
          (gen', r) <- mkListenerRole sig pos gen
          return (Prot { pname = name,
                         pgen = gen',
                         roles = r : rs,
                         psig = sig })
loadProt _ _ _ pos _ =
    fail (shows pos "Malformed protocol")

-- Optionally load a lang field in a protocol.
loadLang :: MonadFail m => Pos -> Sig -> [SExpr Pos] -> m Sig
loadLang pos _ xs | hasKey "lang" xs = loadSig pos (assoc "lang" xs)
loadLang _ sig _ | otherwise = return sig

loadRoles :: MonadFail m => Sig -> Gen -> [SExpr Pos] -> m (Gen, [Role])
loadRoles sig gen (L pos (S _ "defrole" : x) : xs) =
    do
      (gen, r) <- loadRole sig gen pos x
      (gen, rs) <- loadRoles sig gen xs
      return (gen, r : rs)
loadRoles _ gen _ =
    return (gen, [])

loadRole :: MonadFail m => Sig -> Gen -> Pos -> [SExpr Pos] -> m (Gen, Role)
loadRole sig gen _ (S _ name :
                    L _ (S _ "vars" : vars) :
                    L _ (S _ "trace" : evt : c) :
                    _) =
    do
      (gen, vars) <- loadVars sig gen vars
      c <- loadTrace sig vars (evt : c)
      return (gen, Role { rname = name,
                          rvars = vars,
                          rtrace = c })
loadRole _ _ pos _ = fail (shows pos "Malformed role")

loadTrace :: MonadFail m => Sig -> [Term] -> [SExpr Pos] -> m Trace
loadTrace sig vars xs = mapM (loadEvt sig vars) xs

loadEvt :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Event
loadEvt sig vars (L _ [S _ "recv", t]) =
    do
      t <- loadTerm sig vars False t
      return (In $ Plain t)
loadEvt sig vars (L _ [S _ "recv", ch, t]) =
    do
      ch <- loadChan sig vars ch
      t <- loadTerm sig vars False t
      return (In $ ChMsg ch t)
loadEvt sig vars (L _ [S _ "send", t]) =
    do
      t <- loadTerm sig vars False t
      return (Out $ Plain t)
loadEvt sig vars (L _ [S _ "send", ch, t]) =
    do
      ch <- loadChan sig vars ch
      t <- loadTerm sig vars False t
      return (Out $ ChMsg ch t)
loadEvt _ _ (L pos [S _ dir, _]) =
    fail (shows pos $ "Unrecognized direction " ++ dir)
loadEvt _ _ x = fail (shows (annotation x) "Malformed event")

loadChan :: MonadFail m => Sig -> [Term] -> SExpr Pos -> m Term
loadChan sig vars x =
  do
    ch <- loadTerm sig vars False x
    case isChan ch of
      True -> return ch
      False -> fail (shows (annotation x) "Expecting a channel")

-- This is the only place a role is generated with an empty name.
-- This is what marks a strand as a listener.
mkListenerRole :: MonadFail m => Sig -> Pos -> Gen -> m (Gen, Role)
mkListenerRole sig pos g =
  do
    (g, xs) <- loadVars sig g [L pos [S pos "x", S pos "mesg"]]
    case xs of
      [x] -> return (g, Role {
                           rname = "",
                           rvars = [x],
                           rtrace = [In $ Plain x, Out $ Plain x]})
      _ -> fail (shows pos "mkListenerRole: expecting one variable")

---------------------------------------

findSkel :: MonadFail m => Pos -> [Prot] ->
            [SExpr Pos] -> m Skel
findSkel pos ps (S _ name : xs) =
    case L.find (\p -> name == pname p) ps of
      Nothing -> fail (shows pos $ "Protocol " ++ name ++ " unknown")
      Just p -> loadSkel (psig p) pos p xs
findSkel pos _ _ = fail (shows pos "Malformed skeleton")

loadSkel :: MonadFail m => Sig -> Pos -> Prot -> [SExpr Pos] -> m Skel
loadSkel sig pos p (L _ (S _ "vars" : vars) : xs) =
    do
      (gen, kvars) <- loadVars sig (pgen p) vars
      loadStrands sig pos p kvars gen [] xs
loadSkel _ pos _ _ = fail (shows pos "Malformed skeleton")

loadStrands :: MonadFail m => Sig -> Pos -> Prot ->
               [Term] -> Gen -> [Trace] -> [SExpr Pos] -> m Skel
loadStrands sig top p kvars gen insts (L pos (S _ "defstrand" : x) : xs) =
    case x of
      S _ role : N _ height : env ->
          do
            (gen, i) <- loadInst sig pos p kvars gen role height env
            loadStrands sig top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed defstrand")
loadStrands sig top p kvars gen insts (L pos (S _ "deflistener" : x) : xs) =
    case x of
      [term] ->
          do
            t <- loadTerm sig kvars True term
            let i = [In $ Plain t, Out $ Plain t]
            loadStrands sig top p kvars gen (i : insts) xs
      _ ->
          fail (shows pos "Malformed deflistener")
loadStrands _ _ p kvars _ insts xs =
    do
      checkAlist xs -- Ensure alist syntax
      label <- nassoc "label" xs
      parent <- nassoc "parent" xs
      seen <- loadSeen (massoc "seen-ops" xs)
      case label of
        Just l ->
            return Skel { prot = p,
                          kvars = kvars,
                          ktraces = insts,
                          label = l,
                          parent = parent,
                          seen = L.sortOn fst seen,
                          alist = xs }
        Nothing -> fail "Skeleton without a label"

loadInst :: MonadFail m => Sig -> Pos -> Prot -> [Term] -> Gen -> String ->
            Int -> [SExpr Pos] -> m (Gen, Trace)
loadInst sig pos p kvars gen role height env =
    do
      r <- lookupRole pos p role
      case height < 1 || height > length (rtrace r) of
        True -> fail (shows pos "Bad height")
        False ->
            do
              let vars = rvars r
              (gen', env') <- foldM (loadMaplet sig kvars vars)
                              (gen, emptyEnv) env
              return (mkTrace gen' r env' height)

lookupRole :: MonadFail m => Pos -> Prot -> String -> m Role
lookupRole pos p role =
    case L.find (\r -> role == rname r) (roles p) of
      Nothing ->
          fail (shows pos $ "Role " ++ role ++ " not found in " ++ pname p)
      Just r -> return r

loadMaplet :: MonadFail m => Sig -> [Term] -> [Term] ->
              (Gen, Env) -> SExpr Pos -> m (Gen, Env)
loadMaplet sig kvars vars env (L pos [domain, range]) =
    do
      t <- loadTerm sig vars False domain
      t' <- loadTerm sig kvars False range
      case match t t' env of
        env' : _ -> return env'
        [] -> fail (shows pos "Domain does not match range")
loadMaplet _ _ _ _ x = fail (shows (annotation x) "Malformed maplet")

mkTrace :: Gen -> Role -> Env -> Int -> (Gen, Trace)
mkTrace gen role env height =
    let trace = rtrace role
        rheight = length trace in
    if height < 1 || height > rheight then
        error "Db.Loader.mkTrace: Bad strand height"
    else
        let (gen', env') = grow (rvars role) gen env in
        (gen', map (evtMap $ instantiate env') (take height trace))

-- For each term that matches itself in the environment, extend the
-- mapping so that the term maps to one with a fresh set of variables.
-- It is an error if a variable in one of the terms is explicitly
-- mapped to itself in the initial environment.
grow :: [Term] -> Gen -> Env -> (Gen, Env)
grow [] gen env = (gen, env)
grow (t : ts) gen env =
    case match t t (gen, env) of
      [] -> grow ts gen env     -- Term already mapped
      _ ->                      -- Otherwise make a fresh mapping
          let (gen', t') = clone gen t in
          case match t t' (gen', env) of
            (gen'', env') : _ -> grow ts gen'' env'
            [] -> error "Db.Loader.grow: Internal error"

-- Association lists

loadSeen :: MonadFail m => Maybe [SExpr Pos] -> m [(Int, SExpr Pos)]
loadSeen Nothing = return []
loadSeen (Just xs) = mapM loadSeenOp xs

loadSeenOp :: MonadFail m => SExpr Pos -> m (Int, SExpr Pos)
loadSeenOp (L _ [N _ l, x]) = return (l, x)
loadSeenOp (L pos [N _ l]) =
    return (l, L pos [S pos "operation", S pos "new"])
loadSeenOp x = fail (shows (annotation x) "Malformed seen operation")

-- Strip positions from an S-expression

{-
strip :: SExpr a -> SExpr ()
strip (S _ s) = S () s
strip (Q _ s) = Q () s
strip (N _ n) = N () n
strip (L _ l) = L () (map strip l)
-}

-- Ensure alist has the proper form
checkAlist :: MonadFail m => [SExpr Pos] -> m ()
checkAlist [] = return ()
checkAlist ((L _ (S _ _ : _)) : xs) = checkAlist xs
checkAlist xs = fail (shows (annotation $ head xs) "Malformed association list")

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr a] -> [SExpr a]
assoc key alist =
    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]

keyPred :: String -> SExpr a -> Bool
keyPred key (L _ (S _ head : _)) = key == head
keyPred _ _ = False

hasKey :: String -> [SExpr a] -> Bool
hasKey key alist = any (keyPred key) alist

-- Lookup value in alist, appending values with the same key
massoc :: String -> [SExpr Pos] -> Maybe [SExpr Pos]
massoc key alist =
    loop alist Nothing
    where
      loop ((L _ (S _ head : tail)) : rest) vals
          | key == head = loop rest (extend tail vals)
          | otherwise = loop rest vals
      loop _ vals = vals
      extend x Nothing = Just x
      extend x (Just y) = Just (x ++ y)

nassoc :: MonadFail m => String -> [SExpr Pos] -> m (Maybe Int)
nassoc key xs =
    case massoc key xs of
      Nothing -> return Nothing
      Just [val] ->
          do
            ns <- num val
            return (Just ns)
      Just (x:_) -> fail (shows (annotation x) "Expecting one number")
      Just [] -> fail (shows (annotation (head xs)) "Expecting one number")

num :: MonadFail m => SExpr Pos -> m Int
num (N _ n) = return n
num x = fail (shows (annotation x) "Expecting a number")
