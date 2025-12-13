
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Structure.Exception
-- Description : arithmetic exceptions
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- arithmetic exceptions.
module OAlg.Structure.Exception
  ( ArithmeticException(..)
  )
  where

import OAlg.Prelude


--------------------------------------------------------------------------------
-- ArithmeticException -

-- | arithmetic exceptions which are sub exceptions of 'SomeOAlgException'.
data ArithmeticException
  = NotAddable
  | NotMultiplicable
  | NotInvertible
  | UndefinedScalarproduct
  | NotExponential
  | NotEndo
  | NotTransformable
  | NoMinusOne
  | NotApplicable
  deriving (Eq,Show)

instance Exception ArithmeticException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException


