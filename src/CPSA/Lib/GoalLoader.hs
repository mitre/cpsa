-- Loads security goals from S-expressions.

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.GoalLoader (loadSentence) where

import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

loadSentence :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                g -> SExpr Pos -> m (g, Goal t)
loadSentence _ _ g _ = return (g, Goal { antec = [], concl = [] })
