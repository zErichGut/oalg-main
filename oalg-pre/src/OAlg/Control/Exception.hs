{-# LANGUAGE ExistentialQuantification, StandaloneDeriving #-}

-- |
-- Module      : OAlg.Control.Exception
-- Description : general algebraic exceptions
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- General algebraic exceptions.
module OAlg.Control.Exception
  ( -- * Algebraic Exceptions
    oalgExceptionToException
  , oalgExceptionFromException
  , SomeOAlgException(..)
  , AlgebraicException(..)
  , implementation

    -- * Exports
  , Exception(..), throw
  )
  where

import Control.Exception as E
import Data.Typeable (cast)

--------------------------------------------------------------------------------
-- Algebraic exceptions

-- | The root exception for all algebraic exceptions.
data SomeOAlgException = forall e . Exception e => SomeOAlgException e

instance Show SomeOAlgException where
  show (SomeOAlgException e) = show e
  
instance Exception SomeOAlgException

-- | embedding an exception into 'SomeOAlgException'.
oalgExceptionToException :: Exception e => e -> SomeException
oalgExceptionToException = toException . SomeOAlgException

-- | casting an exception to 'SomeOAlgException'.
oalgExceptionFromException :: Exception e => SomeException -> Maybe e
oalgExceptionFromException e = do
  SomeOAlgException a <- fromException e
  cast a

-- | general algebraic exception which are sub exceptions of 'SomeOAlgException'.
data AlgebraicException
  = AlgebraicException String
  | Undefined String
  | ImplementationError String
  | NoPredecor
  | InvalidData String
  deriving (Show)

instance Exception AlgebraicException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- implementation -

-- | message for implementation errors. Mainly used for non-permissible or unreachable
-- patterns.
implementation :: String
implementation = "implementation"
