
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Homology.Eval.Core
-- Description : core definitions for evaluations on homologies.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- core definitions for evaluations on homologies.
module OAlg.Homology.Eval.Core
  (
    Eval, EvalFailure(..), failure
  ) where

import OAlg.Prelude

import OAlg.Data.Either

--------------------------------------------------------------------------------
-- EvalFailure -

-- | evaluation failures.
data EvalFailure
  = IndexOutOfRange Z
  | AtOutOfRange N
  | NotSupportedChainType String
  | NotCycle String
  | NotEligible String
  | EvalFailure String
  deriving (Show)

--------------------------------------------------------------------------------
-- Eval -

type Eval = Either EvalFailure

--------------------------------------------------------------------------------
-- failure -

failure :: EvalFailure -> Eval x
failure = Left

