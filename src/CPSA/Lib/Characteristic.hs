-- Makes the characteristic skeleton of a security goal

-- Copyright (c) 2015 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.Characteristic (characteristic) where

import CPSA.Lib.SExpr
import CPSA.Lib.Algebra
import CPSA.Lib.Protocol
import CPSA.Lib.Goal
import CPSA.Lib.Strand

{--
import System.IO.Unsafe
z :: Show a => a -> b -> b
z x y = unsafePerformIO (print x >> return y)
--}

characteristic :: (Algebra t p g s e c, Monad m) => Pos -> Prot t g ->
                  g -> Goal t -> [SExpr ()] -> m (Preskel t g s e)
characteristic _ _ _ _ _ = fail "bla"
