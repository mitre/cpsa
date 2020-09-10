-- Loads the first protocol

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

{-# LANGUAGE CPP #-}

#if !(MIN_VERSION_base(4,13,0))
#define MonadFail Monad
#endif

module CPSA.Roletran.Loader (loadSExprs) where

import Control.Monad (foldM)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import CPSA.Lib.ReturnFail
import CPSA.Lib.SExpr
import CPSA.Roletran.Algebra
import CPSA.Roletran.Protocol

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)

zz :: Show a => a -> a
zz x = z x x
--}

-- Load protocols and preskeletons from a list of S-expressions, and
-- then return a list of preskeletons.  The name of the algebra is
-- nom, and its variable generator is provided.

loadSExprs :: MonadFail m => [SExpr Pos] -> m Prot
loadSExprs ((L pos (S _ "defprotocol" : xs)) : _) =
  loadProt pos xs
loadSExprs (_ : sexprs) =
  loadSExprs sexprs
loadSExprs [] =
  fail "No protocol found"

loadProt :: MonadFail m => Pos -> [SExpr Pos] -> m Prot
loadProt pos (S _ name : S _ alg : x : xs)
    | alg /= "basic"=
        fail (shows pos "Expecting terms in basic algebra ")
    | otherwise =
        do
          rs <- loadRoles (x : xs)
          -- Check for duplicate role names
          validate (mkProt name pos rs) rs
    where
      validate prot [] = return prot
      validate prot (r : rs) =
          case L.find (\r' -> rname r == rname r') rs of
            Nothing -> validate prot rs
            Just _ ->
                let msg = "Duplicate role " ++ rname r ++
                          " in protocol " ++ name in
                fail (shows pos msg)
loadProt pos _ = fail (shows pos "Malformed protocol")

loadRoles :: MonadFail m => [SExpr Pos] -> m [Role]
loadRoles (L pos (S _ "defrole" : x) : xs) =
    do
      r <- loadRole pos x
      rs <- loadRoles xs
      return (r : rs)
loadRoles _ =
    return []

loadRole :: MonadFail m => Pos -> [SExpr Pos] -> m Role
loadRole pos (S _ name :
              L _ (S _ "vars" : vars) :
              L _ (S _ "trace" : evt : c) :
              rest) =
    do
      declEnv <- loadVars vars
      c <- loadTrace declEnv (evt : c)
      case traceWellFormed c of
        Nothing -> fail (shows pos "Malformed terms")
        Just env ->
          do
            u <- mapM (loadBasic env) (assoc "uniq-orig" rest)
            i <- mapM (loadChanBasic env) (assoc "inputs" rest)
            o <- mapM (loadTerm env) (assoc "outputs" rest)
            mkRole name pos env c u i o
loadRole pos _ = fail (shows pos "Malformed role")

-- Lookup value in alist, appending values with the same key
assoc :: String -> [SExpr a] -> [SExpr a]
assoc key alist =
    concat [ rest | L _ (S _ head : rest) <- alist, key == head ]

loadTrace :: MonadFail m => VarEnv -> [SExpr Pos] -> m Trace
loadTrace env xs = mapM (loadEvt env) xs

loadEvt :: MonadFail m => VarEnv -> SExpr Pos -> m Event
loadEvt env (L pos [S _ "recv", ch, t]) =
    do
      ch <- loadChan env ch
      t <- loadTerm env t
      return (In pos ch t)
loadEvt env (L pos [S _ "send", ch, t]) =
    do
      ch <- loadChan env ch
      t <- loadTerm env t
      return (Out pos ch t)
loadEvt _ (L pos [S _ _, _]) =
    fail (shows pos $ "Missing channel")
loadEvt _ (L pos (S _ dir : _)) =
    fail (shows pos $ "Unrecognized direction " ++ dir)
loadEvt _ x = fail (shows (annotation x) "Malformed event")

-- Variable declarations

loadVars :: MonadFail m => [SExpr Pos] -> m VarEnv
loadVars sexprs =
    do
      pairs <- mapM loadVarPair sexprs
      foldM loadVar emptyVarEnv (concat pairs)

loadVarPair :: MonadFail m => SExpr Pos -> m [(SExpr Pos, SExpr Pos)]
loadVarPair (L _ (x:y:xs)) =
  let (t:vs) = reverse (x:y:xs) in
  return [(v,t) | v <- reverse vs]
loadVarPair x = fail (shows (annotation x) "Bad variable declaration")

loadVar :: MonadFail m => VarEnv -> (SExpr Pos, SExpr Pos) -> m VarEnv
loadVar env (S pos name, S pos' sort) =
  case M.lookup name env of
    Just _ ->
      fail (shows pos "Duplicate variable declaration for " ++ name)
    Nothing ->
      do
        s <- loadSort pos' sort
        return $ M.insert name s env
loadVar _ (x, _) = fail (shows (annotation x) "Bad variable syntax")

loadSort :: MonadFail m => Pos -> String -> m Sort
loadSort pos sort
  | sort == "text" = return Text
  | sort == "data" = return Data
  | sort == "name" = return Name
  | sort == "skey" = return Skey
  | sort == "akey" = return Akey
  | sort == "mesg" = return Mesg
  | sort == "chan" = return Chan
  | otherwise = fail (shows pos "Sort " ++ sort ++ " not recognized")

-- Term loading

loadChan :: MonadFail m => VarEnv -> SExpr Pos -> m Term
loadChan env (S pos v) =
  case M.lookup v env of
    Nothing -> fail (shows pos ("Undeclared variable " ++ v))
    Just Chan -> return (Chn v)
    Just _ -> fail (shows pos "Expecting a channel")
loadChan _ x =
  fail (shows (annotation x) "Expecting a channel")

loadBasic :: MonadFail m => VarEnv -> SExpr Pos -> m Term
loadBasic env x =
    do
      t <- loadTerm env x
      case isBasic t of
        True -> return t
        False -> fail (shows (annotation x) "Expecting a basic value")

loadLookup :: MonadFail m => VarEnv -> Pos -> Var -> m Term
loadLookup env pos v =
  case M.lookup v env of
    Nothing -> fail (shows pos ("Undeclared variable " ++ v))
    Just Text -> return (Txt v)
    Just Data -> return (Dta v)
    Just Name -> return (Nam v)
    Just Skey -> return (Sky (SVar v))
    Just Akey -> return (Aky (AVar v))
    Just Ikey -> fail (shows pos "Not expecting an ikey")
    Just Mesg -> return (Msg v)
    Just Chan -> fail (shows pos "Not expecting a channel")

loadChanBasic :: MonadFail m => VarEnv -> SExpr Pos -> m Term
loadChanBasic env x =
  case loadChan env x of
    Return t -> return t
    Fail _ -> loadBasic env x

loadName :: MonadFail m => VarEnv -> Pos -> Var -> m ()
loadName env pos v =
  do
    t <- loadLookup env pos v
    case sort t of
      Name -> return ()
      _ -> fail (shows pos "Expecting a name")

loadTerm :: MonadFail m => VarEnv -> SExpr Pos -> m Term
loadTerm env (S pos s) =
  loadLookup env pos s
loadTerm _ (Q _ t) =
  return (Tag t)
loadTerm env (L pos (S _ s : l)) =
  case lookup s loadDispatch of
    Nothing -> fail (shows pos "Keyword " ++ s ++ " unknown")
    Just f -> f pos env l
loadTerm _ x = fail (shows (annotation x) "Malformed term")

type LoadFunction m = Pos -> VarEnv -> [SExpr Pos] -> m Term

loadDispatch :: MonadFail m => [(String, LoadFunction m)]
loadDispatch =
    [("pubk", loadPubk)
    ,("privk", loadPrivk)
    ,("invk", loadInvk)
    ,("ltk", loadLtk)
    ,("cat", loadCat)
    ,("enc", loadEnc)
    ,("hash", loadHash)
    ]

-- Atom constructors: pubk privk invk ltk

loadPubk :: MonadFail m => LoadFunction m
loadPubk _ env [S pos s] =
    do
      loadName env pos s
      return $ Aky (Pubk s)
loadPubk _ env [Q _ c, S pos s] =
    do
      loadName env pos s
      return $ Aky (Pubk2 c s)
loadPubk pos _ _ = fail (shows pos "Malformed pubk")

loadPrivk :: MonadFail m => LoadFunction m
loadPrivk _ env [S pos s] =
    do
      loadName env pos s
      return $ Aky (Privk s)
loadPrivk _ env [Q _ c, S pos s] =
    do
      loadName env pos s
      return $ Aky (Privk2 c s)
loadPrivk pos _ _ = fail (shows pos "Malformed privk")

loadInvk :: MonadFail m => LoadFunction m
loadInvk _ env [t] =
    do
      t <- loadTerm env t
      return $ inv t
loadInvk pos _ _ = fail (shows pos "Malformed invk")

loadLtk :: MonadFail m => LoadFunction m
loadLtk _ env [S pos s, S pos' s'] =
    do
      loadName env pos s
      loadName env pos' s'
      return $ Sky (Ltk s s')
loadLtk pos _ _ = fail (shows pos "Malformed ltk")

-- Term constructors: cat enc

loadCat :: MonadFail m => LoadFunction m
loadCat _ env (l : ls) =
    do
      ts <- mapM (loadTerm env) (l : ls)
      return $ foldr1 Pr ts
loadCat pos _ _ = fail (shows pos "Malformed cat")

loadEnc :: MonadFail m => LoadFunction m
loadEnc pos env (l : l' : ls) =
    do
      let (butLast, last) = splitLast l (l' : ls)
      t <- loadCat pos env butLast
      t' <- loadTerm env last
      case isMesgVar t' of
        False -> return $ En t t'
        True -> fail (shows (annotation last)
                      "Message variable cannot used as key")
loadEnc pos _ _ = fail (shows pos "Malformed enc")

splitLast :: a -> [a] -> ([a], a)
splitLast x xs =
    loop [] x xs
    where
      loop z x [] = (reverse z, x)
      loop z x (y : ys) = loop (x : z) y ys

loadHash :: MonadFail m => LoadFunction m
loadHash pos env (l : ls) =
   do
     t <- loadCat pos env (l : ls)
     return $ Hsh t
loadHash pos _ _ = fail (shows pos "Malformed hash")
