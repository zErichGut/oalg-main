
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Eval
-- Description : evaluations for homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- evaluations for homology.
module OAlg.Homology.Eval
  (
  ) where

import Control.Monad

import Data.Kind
import Data.Array

import OAlg.Prelude

import OAlg.Data.Proxy
import OAlg.Data.Either

-- import OAlg.Structure.Distributive
-- import OAlg.Structure.Exponential

-- import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural
-- import OAlg.Entity.FinList
-- import OAlg.Entity.Slice.Free
-- import OAlg.Entity.Matrix

-- import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
-- import OAlg.AbelianGroup.KernelsAndCokernels

-- import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
-- import OAlg.Limes.Exact.Free

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition


import OAlg.Entity.Sequence.Set
--------------------------------------------------------------------------------
-- EvalFailure -

-- | evaluation failures.
data EvalFailure
  = IndexOutOfRange N
  | EvalFailure String
  deriving (Show)

--------------------------------------------------------------------------------
-- Eval -

type Eval = Either EvalFailure

--------------------------------------------------------------------------------
-- failure -

failure :: EvalFailure -> Eval x
failure = Left

--------------------------------------------------------------------------------
-- Env -

data Env t s n x where
  Env :: (Simplical s x, Attestable n)
    => { envDim          :: N
       , envChainComplex :: ChainComplex t Z s n x
       , envHomology     :: Homology n
       , envAt0          :: (ChainComplex t Z s N0 x,Homology N0)
       , envAt           :: Array N (ChainComplex Regular Z s N0 x,Homology N0)
       }
    -> Env t s n x

--------------------------------------------------------------------------------
-- env -

env :: (Simplical s x, Attestable n) => ChainComplexType t -> Any n -> Complex x -> Env t s n x
env t n c = case ats n of
  Ats -> Env { envDim          = dm
             , envChainComplex = cc
             , envHomology     = hm
             , envAt0          = at0
             , envAt           = at
             } where
    dm  = lengthN n
    cc  = chainComplex t n c
    hm  = homology cc
    at0 = (ccxHead cc,vrcHead hm)
    at  = case n of
      W0    -> array (1,0) []
      SW n' -> array (1,dm) $ ascs n' 1 (ccxTail cc) (vrcTail hm)

    ascs :: Simplical s x
      => Any n -> N
      -> ChainComplex Regular Z s n x -> Homology n
      -> [(N,(ChainComplex Regular Z s N0 x,Homology N0))]
    ascs n i cc hm = (i,(ccxHead cc,vrcHead hm)) : case n of
      W0    -> []
      SW n' -> ascs n' (succ i) (ccxTail cc) (vrcTail hm)
   
env' :: (Simplical s x, Attestable n) => q s -> ChainComplexType t -> Any n -> Complex x -> Env t s n x
env' _ = env

t = ChainComplexStandard
n = attest :: Any N6
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N
s = Proxy :: Proxy Asc

ea = env' s t n a
eb = env' s t n b

--------------------------------------------------------------------------------
-- evalMaxDim -

evalMaxDim :: Env t s n x -> N
evalMaxDim = envDim

--------------------------------------------------------------------------------
-- evalCardsSmplSet -

evalCardsSmplSet :: Env t s n x -> Cards Z n
evalCardsSmplSet env@Env{} = ccxCards $ envChainComplex env

--------------------------------------------------------------------------------
-- evalHomologyGroups -

evalHomologyGroups :: Env t s n x -> Deviation (n+1) AbHom
evalHomologyGroups env@Env{} = homologyGroups $ envHomology env

--------------------------------------------------------------------------------
-- evlHomologyAt -

evlHomologyAt :: Env t s n x -> N -> Eval (Homology N0)
evlHomologyAt env i
  | i == 0             = return $ snd $ envAt0 env
  | evalMaxDim env < i = failure $ IndexOutOfRange i
  | otherwise          = return $ snd (envAt env ! i)

--------------------------------------------------------------------------------
-- evalHomologyGroupAt -

evalHomologyGroupAt :: Env t s n x -> N -> Eval AbGroup
evalHomologyGroupAt env i = evlHomologyAt env i >>= return . deviationTo


--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = MaxDimExpr -- ^ the maximal dimension
  | CardExpr  (CardinalityExpression t s n x) -- ^ cardinality.
  | HomologyGroupExpr (HomologyGroupExpression t s n x)

--------------------------------------------------------------------------------
-- CardExpression -

-- | expression to evaluate values of type t'Cardinality'.
data CardinalityExpression (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = CardSimplexSetExpr

--------------------------------------------------------------------------------
-- HomologyGroupExpression -

-- | expression to evaluate values of type t'HomologyGroup'.
data HomologyGroupExpression (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = HomologyGroupsAllExpr
  | HomologyGroupAtExpr N

--------------------------------------------------------------------------------
-- Value -

data Value (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = MaximalDimension N
  | Cardinality (Cardinality t s n x)
  | HomologyGroup (HomologyGroup t s n x)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Cardinality -

data Cardinality (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = SimplexSetCardinalities (Cards Z n)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup (t :: Regularity) (s :: Type -> Type) (n :: N') x
  = HomologyGroups (Deviation (n+1) AbHom)
  | HomologyGroupAt (AbGroup)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- evalCardExpr -

evalCardExpr :: Env t s n x -> CardinalityExpression t s n x -> Eval (Cardinality t s n x)
evalCardExpr env cexpr = case cexpr of
  CardSimplexSetExpr -> return $ SimplexSetCardinalities $ evalCardsSmplSet env 

--------------------------------------------------------------------------------
-- evalHomologyGroupExpr -

evalHomologyGroupExpr :: Env t s n x -> HomologyGroupExpression t s n x -> Eval (HomologyGroup t s n x)
evalHomologyGroupExpr env hexpr = case hexpr of
  HomologyGroupsAllExpr -> return $ HomologyGroups $ evalHomologyGroups env
  HomologyGroupAtExpr i -> evalHomologyGroupAt env i >>= return . HomologyGroupAt
--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> Expression t s n x -> Eval (Value t s n x)
eval env expr = case expr of
  MaxDimExpr     -> return $ MaximalDimension $ evalMaxDim env
  CardExpr cexpr -> evalCardExpr env cexpr >>= return . Cardinality
  HomologyGroupExpr hexpr -> evalHomologyGroupExpr env hexpr >>= return . HomologyGroup
