-- Contains MonadFail friendly version of Either String.

-- Copyright (c) 2009 The MITRE Corporation
--
-- This program is free software: you can redistribute it and/or
-- modify it under the terms of the BSD License as published by the
-- University of California.

module CPSA.Lib.ReturnFail where

-- Like Either String but with fail method defined
data ReturnFail a
    = Return a
    | Fail String

instance Functor ReturnFail where
    fmap _ (Fail x)   = Fail x
    fmap f (Return y) = Return (f y)

instance Applicative ReturnFail where
    pure           = Return
    Fail e <*> _   = Fail e
    Return f <*> r = fmap f r

instance Monad ReturnFail where
    Fail l >>= _   = Fail l
    Return r >>= k = k r

instance MonadFail ReturnFail where
    fail s         = Fail s
