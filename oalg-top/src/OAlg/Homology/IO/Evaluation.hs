
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
-- Description : evaluation
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 
module OAlg.Homology.IO.Evaluation
  () where

import Control.Monad
-- import Control.Applicative
-- import Control.Exception

-- import System.IO

import Data.Typeable
import Data.List ((++),reverse,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList,foldl)
import qualified Data.Map.Strict as M

import OAlg.Prelude -- hiding (Result(..), It,(:>:))

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Vectorial
import OAlg.Structure.Exception

import OAlg.Hom.Oriented

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Homology.IO.Pretty
import OAlg.Homology.IO.Term

--------------------------------------------------------------------------------
-- Env -

type EnvH n x = M.Map N (SomeHomology n x)

type EnvV x = M.Map String (Term x)

data Env x where
  Env :: N -> N -> EnvV x -> EnvH n x -> Value x -> Env x

initEnv :: (Entity x, Ord x, Attestable n) => N -> Regular -> Complex n x -> Env x
initEnv dMax r c = Env 0 dMax M.empty mhs (ZValue 0) where
  ChainHomology hs = homology r c
  mhs = M.fromAscList ([0..] `zip` (reverse $ toList hs))

--------------------------------------------------------------------------------
-- envDepth -

envDepth :: Env x -> N
envDepth (Env d _ _ _ _) = d

--------------------------------------------------------------------------------
-- envDepthMax -

envDepthMax :: Env x -> N
envDepthMax (Env _ dMax _ _ _) = dMax

--------------------------------------------------------------------------------
-- envSucc -

envSucc :: Env x -> Env x
envSucc (Env d dMax vs hs it) = Env (succ d) dMax vs hs it

--------------------------------------------------------------------------------
-- (??) -

(??) :: Env x -> String -> Maybe (Term x)
(??) (Env _ _ vs _ _) v = M.lookup v vs

--------------------------------------------------------------------------------
-- envInsert -

envInsert :: Env x -> String -> Term x -> Env x
envInsert (Env d dMax vs hs it) v t = Env d dMax vs' hs it where vs' = M.insert v t vs

--------------------------------------------------------------------------------
-- EvaluationFailuer -

data EvaluationFailure where
  UnboundVariable :: Pretty t => t -> EvaluationFailure
  NotAZValue :: Pretty t =>  t -> EvaluationFailure
  MaxDepthReached :: N -> EvaluationFailure

  UnresolvedLet ::  Pretty t => t -> EvaluationFailure
  NotAddableTerm :: Pretty t => t -> EvaluationFailure
  NotAValue :: Pretty t => t -> EvaluationFailure
  UndefinedFailure :: Pretty x => String -> x -> EvaluationFailure

instance Pretty EvaluationFailure where
  pshow (UndefinedFailure msg x) = "undefined failuer " ++ msg ++ ": " ++ pshow x

--------------------------------------------------------------------------------
-- failure -

failure :: EvaluationFailure -> Eval x
failure = Left

--------------------------------------------------------------------------------
-- Eval -

type Eval x = Either EvaluationFailure x

--------------------------------------------------------------------------------
-- evalZValue -

evalZValue :: (Entity x, Ord x) => Env x -> Term x -> Eval Z
evalZValue e t = do
  v <- eval e t
  case v of
    ZValue z -> return z
    _        -> failure $ NotAZValue t

--------------------------------------------------------------------------------
-- ($>>) -

($>>) :: (Entity x, Ord x) => Value x -> Value x -> Eval (Value x)
($>>) = error "nyi"

--------------------------------------------------------------------------------
-- evalSumForm -

evalSumForm :: (Entity x, Ord x) => Env x -> Term x -> Eval (SumForm Z (Value x))
evalSumForm e _ | envDepthMax e <= envDepth e = failure $ MaxDepthReached $ envDepthMax e 
evalSumForm e t                               = case t of
  z :!> a -> do
    z' <- evalZValue e' z
    a' <- evalSumForm e' a
    return (z' :! a')
    where e' = envSucc e
    
  a :+> b -> do
    a' <- evalSumForm e' a
    b' <- evalSumForm e' b
    return (a' :+ b')
    where e' = envSucc e
    
  _ -> eval e t >>= return . S

--------------------------------------------------------------------------------
-- evalSum -
evalSum :: (Entity x, Ord x) => SumForm Z (Value x) -> Eval (Value x)
evalSum = error "nyi"

--------------------------------------------------------------------------------
-- eval -

eval :: (Entity x, Ord x) => Env x -> Term x -> Eval (Value x)
eval e _ | envDepthMax e <= envDepth e = failure $ MaxDepthReached $ envDepthMax e 
eval e t                               = case t of
  Free a -> case e ?? a of
    Just t' -> eval e t'
    Nothing -> failure $ UnboundVariable t

  Let a t t' -> eval e' t' where e' = envInsert e a t

  Value v -> return v

  f :>> x -> do
    f' <- eval e' f
    x' <- eval e' x
    f' $>> x'
    where e' = envSucc e

  z :!> a -> do
    z' <- evalZValue e' z
    a' <- evalSumForm e' a
    evalSum (z' :! a')
    where e' = envSucc e

  a :+> b -> do
    a' <- evalSumForm e' a
    b' <- evalSumForm e' b
    evalSum (a' :+ b')
    where e' = envSucc e

