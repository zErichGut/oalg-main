
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

import OAlg.AbelianGroup.Definition

--------------------------------------------------------------------------------
-- EvalFailure -

-- | evaluation failures.
data EvalFailure
  = IndexOutOfRange String
  | AtOutOfRange Z
  | NotSupportedChainType String
  | NotCycle String
  | NotEligible String
  | UnboundVariable Z String
  | NotAddableExpression
  | NotAChainType
  | NonZeroHomologyClass AbElement
  | RecursiveDefinition String
  | EvalFailure String
  deriving (Show)

--------------------------------------------------------------------------------
-- Eval -

type Eval = Either EvalFailure

--------------------------------------------------------------------------------
-- failure -

failure :: EvalFailure -> Eval x
failure = Left

