{-|
Module:      CPSA.Haskell.Runtime
Description: Runtime for Roletran generated procedures
Copyright:   (c) 2021 The MITRE Corporation
License:     BSD

This module defines the interface between Roletran generated
procedures and the implementation of a runtime system.

-}

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module CPSA.Haskell.Runtime where

import System.IO (Handle)

-- | There are no constraints on what is used to represent a message.

class Mesg m

-- | Types of messages

data Type
  = Text                        -- ^ Plaintext
  | Data                        -- ^ Data
  | Name                        -- ^ Name
  | Skey                        -- ^ Symmetric key
  | Akey                        -- ^ Public asymmetric key
  | Ikey                        -- ^ Private asymmetric key
  | Mesg                        -- ^ Message -- top kind for terms
  | Quot                        -- ^ Tag
  | Pair                        -- ^ Pair
  | Senc                        -- ^ Symmetric encryption
  | Aenc                        -- ^ Asymmetric encryption
  | Ienc                        -- ^ Sign
  | Hash                        -- ^ Hash
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | A runtime provides a set of expressions and statements.

class Mesg m => Runtime r m | m -> r, r -> m where

  -- ^ EXPRESSIONS

  -- | Construct a pair.  The types specify the inputs.
  pair :: r -> Type -> Type -> m -> m -> IO (m, r)

  -- | Project first component of pair.  The type specifies the output.
  frst :: r -> Type -> m -> IO (m, r)

  -- | Project second component of pair.  The type specifies the output.
  scnd :: r -> Type -> m -> IO (m, r)

  -- | Encrypt plain text.  The types specify the inputs.
  encr :: r -> Type -> Type -> m -> m -> IO (m, r)

  -- | Decrypt cipher text.  The first type species the output, and
  -- the second type specifies key, the last argument.
  decr :: r -> Type -> Type -> m -> m -> IO (m, r)

  -- | Construct a tag.
  tag :: r -> String -> IO (m, r)

  -- | Construct a hash.  The type specifies the input.
  hash :: r -> Type -> m -> IO (m, r)

  -- | Generate a fresh nonce.  The type specifies the output.
  frsh :: r -> Type -> IO (m, r)

  -- | Receive a message.  The type specifies the output.
  recv :: r -> Type -> Handle -> IO (m, r)

  -- ^ STATEMENTS

  -- | Send a message.  The type specifies the input.
  send :: r -> Type -> Handle -> m -> IO r

  -- | Check the type of a message.
  chck :: r -> Type -> m -> IO r

  -- | Are two values the same?  The type specifies the inputs.
  same :: r -> Type -> m -> m -> IO r

  -- | Values related by the ltk function?  Is the first input a
  -- symmetric key named by the remaining inputs?
  ltkp :: r -> m -> m -> m -> IO r

  -- | Values related by the invk function?  The type specifies the
  -- first input.
  invp :: r -> Type -> m -> m -> IO r

  -- | Values related by the pubk function?  The first input is an
  -- asymmetric key and the second input is a name.  The type
  -- specifies the first input.
  namp :: r -> Type -> m -> m -> IO r

  -- | Values related by the pubk2 function?  The first input is an
  -- asymmetric key, the second input is a tag, and the third input is
  -- a name.  The type specifies the first input.
  nmp2 :: r -> Type -> m -> m -> m -> IO r
