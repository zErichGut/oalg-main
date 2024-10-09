
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Evaluation
-- Description : evaluation of terms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- evaluatoin of 'Term's.
module OAlg.Homology.IO.Evaluation
  (
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Entity.Natural
import OAlg.Entity.Sum

import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex (Regular(..))

import OAlg.Homology.IO.Value
import OAlg.Homology.IO.Term

import OAlg.Structure.Additive
import OAlg.Structure.Vectorial

--------------------------------------------------------------------------------
-- VectorOperation -

data VectorOperation
  = ScalarMultiplication
  | Addition
  deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- TermValue -

type TermValue x = Term VectorOperation (Value x)

--------------------------------------------------------------------------------
-- Env -

data Env n x = Env (EnvT VectorOperation (Value x)) (EnvV n x)

--------------------------------------------------------------------------------
-- env -

env :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> Env n x
env r c = Env (envT ts) (envV r c) where
  ts = []

--------------------------------------------------------------------------------
-- EvaluationFailure -

data EvaluationFailure x
  = ValueFailure (ValueFailure x) (TermValue x)
  | EvaluationFailure (TermValue x)
  deriving (Show)
--------------------------------------------------------------------------------
-- Eval -

type Eval x = Either (EvaluationFailure x)

toEval :: TermValue x -> EvalV x y -> Eval x y
toEval _ (Right y) = Right y
toEval t (Left e)  = Left $ ValueFailure e t

--------------------------------------------------------------------------------
-- evalVZ -

evalVZ :: TermValue x -> Eval x Z
evalVZ (Value (ZValue z)) = return z
evalVZ (Opr o v w)        = case o of
  ScalarMultiplication   -> do v' <- evalVZ v
                               w' <- evalVZ w
                               return (v' ! w')
  Addition               -> do v' <- evalVZ v
                               w' <- evalVZ w
                               return (v' + w')
evalVZ t                 = Left $ EvaluationFailure t

--------------------------------------------------------------------------------
-- evalVSumForm -

evalVSumForm :: TermValue x -> Eval x (SumForm Z (Value x))
evalVSumForm (Opr o v w) = case o of
  ScalarMultiplication -> do z  <- evalVZ v
                             w' <- evalVSumForm w
                             return (z :! w')
  Addition             -> do v' <- evalVSumForm v
                             w' <- evalVSumForm w
                             return (v' :+ w')
evalVSumForm t           = Left $ EvaluationFailure t

--------------------------------------------------------------------------------
-- evalV -

-- | pre: TermValue is in normal form
evalV :: (Entity x, Ord x) => EnvV n x -> TermValue x -> Eval x (Value x)
evalV hs t@(Value u :!> Value v) = toEval t $ evalApplValue hs u v
evalV hs (t :!> Value v) = evalV hs t >>= \u -> evalV hs (Value u :!> Value v)
evalV hs (Value u :!> t) = evalV hs t >>= \v -> evalV hs (Value u :!> Value v)
evalV _ t@(Opr _ _ _)    = evalVSumForm t >>= toEval t . evalSumValue 
evalV _ t                = Left $ EvaluationFailure t

--------------------------------------------------------------------------------
-- evalValue -

evalValue :: (Entity x, Ord x) => Env n x -> TermValue x -> Eval x (Value x)
evalValue (Env vs hs) t = evalV hs (eval $ inst vs t)

  
