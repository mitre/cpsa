-- Performs a data flow analysis of traces in protocol roles

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Parameters.Flow (dataFlow) where

import CPSA.Lib.CPSA

dataFlow :: (Algebra t p g s e c, Monad m) => String -> g ->
            SExpr Pos -> m (SExpr ())
dataFlow nom origin (L pos (S _ "defprotocol" :
                            S _ name :
                            S _ alg :
                            xs))
    | nom == alg =
        do
          xs <- mapM (mapRole origin) xs
          return (L () (S () "defprotocol" :
                        S () name :
                        S () alg :
                        xs))
    | otherwise = fail (shows pos $ "Expecting terms in algebra " ++ nom)
dataFlow _ _ x = return (strip x)

-- Strip positions from an S-expression

strip :: SExpr a -> SExpr ()
strip (S _ s) = S () s
strip (Q _ s) = Q () s
strip (N _ n) = N () n
strip (L _ l) = L () (map strip l)

mapRole :: (Algebra t p g s e c, Monad m) => g ->
           SExpr Pos -> m (SExpr ())
mapRole gen (L _ (S _ "defrole" :
                  S _ name :
	          L _ (S _ "vars" : vars) :
                  L _ (S _ "trace" : trace) :
                  rest)) =
    do
      (_, vs) <- loadVars gen vars
      c <- loadTrace vs trace
      let rest' = addParams (displayParams vs (flow c)) (map strip rest)
      trace <- mapM stripEvt trace
      return (L () (S () "defrole" :
                    S () name :
	            L () (S () "vars" : map strip vars) :
                    L () (S () "trace" : trace) :
                    rest'))
mapRole _ x = return (strip x)

loadTrace :: (Algebra t p g s e c, Monad m) => [t] ->
             [SExpr Pos] -> m [Event t]
loadTrace vars xs = mapM (loadEvt vars) xs

loadEvt :: (Algebra t p g s e c, Monad m) => [t] ->
          SExpr Pos -> m (Event t)
loadEvt vars (L _ [S _ "recv", t]) =
    do
      t <- loadTerm vars t
      return (In t)
loadEvt vars (L _ [S _ "send", t]) =
    do
      t <- loadTerm vars t
      return (Out t)
loadEvt _ (L pos [S _ dir, _]) =
    fail (shows pos $ "Unrecognized direction " ++ dir)
loadEvt _ x = fail (shows (annotation x) "Malformed direction")

displayParams :: Algebra t p g s e c => [t] -> [[t]] -> [SExpr ()]
displayParams vs inits =
    map (L () . map (displayTerm ctx)) inits
    where
      ctx = addToContext emptyContext vs

addParams :: [SExpr ()] -> [SExpr ()] -> [SExpr ()]
addParams inits rest =
    filter notParams rest ++ [L () (S () "parameters" : inits)]
    where
      notParams (L () (S () "parameters" : _)) = False
      notParams _ = True

stripEvt ::Monad m => SExpr Pos -> m (SExpr ())
stripEvt (L _ [S _ "send", t]) = return (L () [S () "send", strip t])
stripEvt (L _ [S _ "recv", t]) = return (L () [S () "recv", strip t])
stripEvt x = fail (shows (annotation x) "Malformed direction")
