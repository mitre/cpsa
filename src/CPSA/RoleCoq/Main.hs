-- Main routine for cpsa4rolecoq

-- Copyright (c) 2020 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module Main (main) where

import System.IO
import Data.Map (toAscList)
import CPSA.Lib.Entry
import CPSA.Lib.Expand
import CPSA.Roletran.Algebra
import CPSA.Roletran.Protocol
import CPSA.Roletran.Loader
import CPSA.Roletran.Emitter (displayPos)
import CPSA.Lib.Pretty

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      sexprs <- readSExprs p
      prot <- tryRun (loadSExprs sexprs)
      h <- outputHandle output
      tryRun (emit h margin prot)
      hClose h

tryRun :: IO a -> IO a
tryRun x =
  do
    y <- tryIO x
    case y of
      Right z -> return z
      Left err -> abort err

-- Emitter

-- Emit a protocol
emit :: Handle -> Int -> Prot -> IO ()
emit h margin prot =
  do
    hPutStrLn h ("(** Protocol: " ++ pname prot ++
                  " (" ++ displayPos (ppos prot) ++ ") *)")
    hPutStrLn h ""
    hPutStrLn h "Require Import String List Alg Role."
    hPutStrLn h "Import List.ListNotations."
    hPutStrLn h "Open Scope list_scope."
    hPutStrLn h "Open Scope string."
    mapM_ (emitRole h margin) (roles prot)

-- Emit a role
emitRole :: Handle -> Int -> Role -> IO ()
emitRole h margin role =
  do
    hPutStrLn h ""
    hPutStrLn h ("(** Role: " ++  rname role ++
                 " (" ++ displayPos (rpos role) ++ ") *)")
    hPutStrLn h ""
    hPutStrLn h ("Definition " ++ (dehyphen $ rname role) ++ "_role: role :=")
    hPutStrLn h "  mkRole"
    let env = makeEnv $ rvars role
    hPutStrLn h (pretty margin $ map (event env) (rtrace role))
    hPutStrLn h (pretty margin $ map (term env) (map fst $ runiques role))
    hPutStrLn h (pretty margin $ map (term env) (rinputs role))
    hPutStr h (pretty margin $ map (term env) (routputs role))
    hPutStrLn h "."

dehyphen :: String -> String
dehyphen [] = []
dehyphen ('-' : cs) = '_' : dehyphen cs
dehyphen (c : cs) = c : dehyphen cs

type Env = [(String, Int)]

makeEnv :: VarEnv -> Env
makeEnv env =
  zip (map fst $ toAscList env) [0 ..]

event :: Env -> Event -> Pretty
event env (In _ ch x) =
  blo 0 [str "Rv ", chan env ch, str " (", term env x, str ")"]
event env (Out _ ch x) =
  blo 0 [str "Sd ", chan env ch, str " (", term env x, str ")"]

chan :: Env -> Term -> Pretty
chan env (Chn v) = str (var env v)
chan _ _ = str "-1"             -- This should never happen

term :: Env -> Term -> Pretty
term env (Txt v) = str ("Tx " ++ var env v)
term env (Dta v) = str ("Dt " ++ var env v)
term env (Nam v) = str ("Nm " ++ var env v)
term env (Sky k) = skey env k
term env (Aky k) = akey env k
term env (Iky k) = ikey env k
term env (Msg v) = str ("Mg " ++ var env v)
term _ (Tag s) = str ("Tg \"" ++ s ++ "\"")
term env (Pr x y) =
  blo 3 [str "Pr (", term env x, str ")",
         brk 1, str "(", term env y, str ")"]
term env (En x y) =
  blo 3 [str "En (", term env x, str ")",
         brk 1, str "(", term env y, str ")"]
term env (Hsh x) = blo 0 [str "Hs (", term env x, str ")"]
term env (Chn v) = str ("Ch " ++ var env v)

skey :: Env -> Skey -> Pretty
skey env (SVar v) = str ("Sk (Sv " ++ var env v ++ ")")
skey env (Ltk v w) =
  str ("Sk (Lt " ++ var env v ++ " " ++ var env w ++ ")")

akey :: Env -> Akey -> Pretty
akey env (AVar v) = str ("Ak (Av " ++ var env v ++ ")")
akey env (Pubk v) = str ("Ak (Pb " ++ var env v ++ ")")
akey env (Pubk2 s v) =
  str ("Ak (Pb2 \"" ++ s ++ "\" " ++ var env v ++ ")")

ikey :: Env -> Akey -> Pretty
ikey env (AVar v) = str ("Ik (Av " ++ var env v ++ ")")
ikey env (Pubk v) = str ("Ik (Pb " ++ var env v ++ ")")
ikey env (Pubk2 s v) =
  str ("Ik (Pb2 \"" ++ s ++ "\" " ++ var env v ++ ")")

var :: Env -> Var -> String
var env v =
  case lookup v env of
    Just i -> show i
    Nothing -> "-1"             -- This should never happen

-- Print a list in which a break cause all breaks to be taken.
list :: [Pretty] -> Pretty
list [] = str "  []"
list (x: xs) =
  grp 3 (str "  [" : x : loop xs)
  where
    loop [] = [str "]"]
    loop (x : xs) = str ";" : brk 1 : x : loop xs

pretty :: Int -> [Pretty] -> String
pretty margin xs =
  pr margin (list xs) ""
