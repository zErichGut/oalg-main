
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
-- evaluatoin of 'Term's of 'Value's..
module OAlg.Homology.IO.Evaluation
  ( evalValue, TermValue, VectorOperation(..)
  , env, envV' , envAlter, Env()
  , Eval, EvaluationFailure(..)
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Structure.Fibred

import OAlg.Entity.Natural hiding (S)
import OAlg.Entity.Sum

import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex (Regular(..))

import OAlg.Homology.IO.Value
import OAlg.Homology.IO.Term

--------------------------------------------------------------------------------
-- VectorOperation -

-- | vector operations.
data VectorOperation
  = ScalarMultiplication
  | Addition
  deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- TermValue -

-- | value-term
type TermValue x = Term VectorOperation (Value x)

--------------------------------------------------------------------------------
-- TermValueRoot -

type TermValueRoot x = Term VectorOperation (ValueRoot x)

--------------------------------------------------------------------------------
-- Env -

-- | evaluation environment.
data Env n x = Env (EnvT VectorOperation (Value x)) (EnvV n x)

--------------------------------------------------------------------------------
-- envV' -

envV' :: Env n x -> EnvV n x
envV' (Env _ hs) = hs

--------------------------------------------------------------------------------
-- env -

-- | creates the environment for a given complex.
env :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> Env n x
env r c = Env (envT ts) hs where
  hs = envV r c
  ts = [ ("homologyGroups",Value hgs)
       , ("chains",Value gch)

         -- operators
       , ("span",Value $ OperatorValue SpanOperator)
       ]

  hgs = valHomologyGroups hs
  gch = valGenerator hs (ChainGenerator ChainGenerator')

--------------------------------------------------------------------------------
-- envAlter -

envAlter :: Env n x -> String -> Value x -> Env n x
envAlter (Env eT hs) s v = Env eT' hs where
  eT' = envTAlter eT s (Value v)


--------------------------------------------------------------------------------
-- EvaluationFailure -

-- | failures of evaluating a value-term to its value.
data EvaluationFailure x
  = ValueFailure (ValueFailure x) (TermValueRoot x)
  | NotAValue (TermValueRoot x)
  | NotAZValue (TermValueRoot x)
  deriving (Show)

--------------------------------------------------------------------------------
-- Eval -

-- | the evaluation-monad.
type Eval x = Either (EvaluationFailure x)

toEval :: (Entity x, Ord x) => TermValue x -> EvalV x y -> Eval x y
toEval _ (Right y) = Right y
toEval t (Left e)  = Left $ ValueFailure e $ fmap root t

--------------------------------------------------------------------------------
-- evalVZ -

evalVZ :: (Entity x, Ord x) => Value x -> Eval x Z
evalVZ (ZValue z) = return z
evalVZ v          = Left $ NotAZValue $ fmap root $ Value v

--------------------------------------------------------------------------------
-- evalVSumForm -

-- | evaluates the sum-form.
evalVSumForm :: (Entity x, Ord x) => EnvV n x -> TermValue x -> Eval x (SumForm Z (Value x))
evalVSumForm hs (Opr o v w) = case o of
  ScalarMultiplication -> do z  <- evalV hs v >>= evalVZ
                             w' <- evalVSumForm hs w
                             return (z :! w')
  Addition             -> do v' <- evalVSumForm hs v
                             w' <- evalVSumForm hs w
                             return (v' :+ w')
evalVSumForm hs t = evalV hs t >>= return . S

--------------------------------------------------------------------------------
-- evalV -

-- | evaluates a value-term to its value, according to the given environment.
--
-- ["Pre"] the given value-term is in normal form.
evalV :: (Entity x, Ord x) => EnvV n x -> TermValue x -> Eval x (Value x)
evalV hs r@(s :!> t)   = evalV hs s >>= \u -> evalV hs t >>= \v -> toEval r $ evalApplValue hs u v
evalV hs r@(Opr _ _ _) = evalVSumForm hs r >>= toEval r . evalSumValue
evalV _ (Value v)      = return v
evalV _ t              = Left $ NotAValue $ fmap root t

--------------------------------------------------------------------------------
-- evalValue -

-- | evaluates a value-term to its value, according to the given environment.
evalValue :: (Entity x, Ord x) => Env n x -> TermValue x -> Eval x (Value x)
evalValue (Env vs hs) t = evalV hs (eval $ inst vs t)

  
--------------------------------------------------------------------------------

{-
-- e r = env r (complex kleinBottle)
e r n = env r (complex (sphere n (0::N)))
z x = Value (ZValue x)

infixr 8 !
infixr 6 +

(!) = Opr ScalarMultiplication
(+) = Opr Addition
-}
