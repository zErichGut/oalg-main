
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
import Data.List as L (zip)

import OAlg.Prelude

import OAlg.Data.Proxy
import OAlg.Data.Either

import OAlg.Structure.Oriented
-- import OAlg.Structure.Distributive
-- import OAlg.Structure.Exponential

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
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
import OAlg.Homology.ChainOperator
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
-- ChainComplexHomology -

-- | ignoring the 'ChainComplexType'.
data SomeChainComplex r s n x where
  SomeChainComplex ::  ChainComplex t r s n x -> SomeChainComplex r s n x

--------------------------------------------------------------------------------
-- Env -

data Env t s n x where
  Env :: (Simplical s x, Attestable n)
    => { envDimMax       :: N
       , envChainComplex :: ChainComplex t Z s n x
       , envHomology     :: Homology n
       , envAt           :: Array N (SomeChainComplex Z s N0 x, Homology N0)
       }
    -> Env t s n x

--------------------------------------------------------------------------------
-- env -

env :: (Simplical s x, Attestable n) => ChainComplexType t -> Any n -> Complex x -> Env t s n x
env t n c = case ats n of
  Ats -> Env { envDimMax       = dm
             , envChainComplex = ccx
             , envHomology     = hmg
             , envAt           = at
             } where
    dm  = lengthN n
    ccx = chainComplex t n c
    hmg = homology ccx
    at  = array (0,dm) $ ascs n 0 ccx hmg

    ascs :: Simplical s x
      => Any n -> N
      -> ChainComplex t Z s n x -> Homology n
      -> [(N,(SomeChainComplex Z s N0 x,Homology N0))]
    ascs n i cc hm = (i,(SomeChainComplex $ ccxHead cc,vrcHead hm)) : case n of
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
-- evalAt -

evalAt :: Env t s n x -> N -> Eval (SomeChainComplex Z s N0 x,Homology N0)
evalAt env i
  | envDimMax env < i = failure $ IndexOutOfRange i
  | otherwise         = return $ (envAt env ! i)

--------------------------------------------------------------------------------
-- evalMaxDim -

evalMaxDim :: Env t s n x -> N
evalMaxDim = envDimMax

--------------------------------------------------------------------------------
-- evalCardSmplSetAll -

evalCardSmplSetAll :: Env t s n x -> Cards Z n
evalCardSmplSetAll env@Env{} = ccxCards $ envChainComplex env

--------------------------------------------------------------------------------
-- evalCardSmplSetAt ´-

evalCardSmplSetAt :: Env t s n x -> N -> Eval (Cards Z N0)
evalCardSmplSetAt env@Env{} i = do
  SomeChainComplex ccx <- evalAt env i >>= return . fst
  return $ ccxCards ccx
  
--------------------------------------------------------------------------------
-- evalHomologyGroups -

evalHomologyGroups :: Env t s n x -> Deviation (n+1) AbHom
evalHomologyGroups env@Env{} = homologyGroups $ envHomology env

--------------------------------------------------------------------------------
-- evalHomologyGroupAt -

evalHomologyGroupAt :: Env t s n x -> N -> Eval (Deviation N1 AbHom)
evalHomologyGroupAt env i = evalAt env i >>= return . homologyGroups . snd

--------------------------------------------------------------------------------
-- evalChainBaseAt -

evalChainBaseAt :: Env t s n x -> N -> Eval (Array N (ChainG Z s x))
evalChainBaseAt env@Env{} i = do
  SomeChainComplex ccx <- evalAt env i >>= return . fst
  case ccx of
    ChainComplex _ (DiagramChainTo _ (d:|_))
      -> return $ array rng $ ([0..] `L.zip` ((\(Set sxs) -> amap1 ch sxs) ssxs)) where
           ssxs = start d
           rng  = case lengthN ssxs of
                    0 -> (1,0)
                    c -> (0,pred c)
  
--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression
  = MaxDimExpr -- ^ the maximal dimension
  | CardinalityExpr  CardinalityExpression -- ^ cardinality.
  | HomologyGroupExpr HomologyGroupExpression
  | ChainExpr ChainExpression

--------------------------------------------------------------------------------
-- CardinalityExpression -

-- | expression to evaluate values of type t'Cardinality'.
data CardinalityExpression
  = CardSimplexSetAllExpr
  | CardSimplexSetAtExpr N

--------------------------------------------------------------------------------
-- HomologyGroupExpression -

-- | expression to evaluate values of type t'HomologyGroup'.
data HomologyGroupExpression
  = HomologyGroupAllExpr
  | HomologyGroupAtExpr N

--------------------------------------------------------------------------------
-- ChainExpression -

data ChainExpression
  = ChainBaseAtExpr N
  | ChainAtExpr N
  
--------------------------------------------------------------------------------
-- Value -

data Value (s :: Type -> Type) x
  = MaximalDimension N
  | Cardinality (Cardinality s x)
  | HomologyGroup (HomologyGroup s x)
  | ChainValue (ChainValue s x)
  deriving (Show)

--------------------------------------------------------------------------------
-- Cardinality -

data Cardinality (s :: Type -> Type) x where
  SimplexSetCardinalities :: Attestable n => Cards Z n -> Cardinality s x

deriving instance Show (Cardinality s x)

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup (s :: Type -> Type) x where
  HomologyGroups :: Attestable n => Deviation (n+1) AbHom -> HomologyGroup s x

deriving instance Show (HomologyGroup s x)

--------------------------------------------------------------------------------
-- ChainValue -

data ChainValue s x
  = ChainGenerator (Array N (ChainG Z s x))
  deriving (Show)
--------------------------------------------------------------------------------
-- evalCardinalityExpr -

evalCardinalityExpr :: Env t s n x -> CardinalityExpression -> Eval (Cardinality s x)
evalCardinalityExpr env@Env{} cexpr = case cexpr of
  CardSimplexSetAllExpr  -> return $ SimplexSetCardinalities $ evalCardSmplSetAll env
  CardSimplexSetAtExpr i -> evalCardSmplSetAt env i >>= return . SimplexSetCardinalities 

--------------------------------------------------------------------------------
-- evalHomologyGroupExpr -

evalHomologyGroupExpr :: Env t s n x -> HomologyGroupExpression -> Eval (HomologyGroup s x)
evalHomologyGroupExpr env@Env{} hexpr = case hexpr of
  HomologyGroupAllExpr  -> return $ HomologyGroups $ evalHomologyGroups env
  HomologyGroupAtExpr i -> evalHomologyGroupAt env i >>= return . HomologyGroups

--------------------------------------------------------------------------------
-- evalChainExpr -

evalChainExpr :: Env t s n x -> ChainExpression -> Eval (ChainValue s x)
evalChainExpr env cexpr = case cexpr of
  ChainBaseAtExpr i -> evalChainBaseAt env i >>= return . ChainGenerator
--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> Expression -> Eval (Value s x)
eval env expr = case expr of
  MaxDimExpr              -> return $ MaximalDimension $ evalMaxDim env
  CardinalityExpr cexpr   -> evalCardinalityExpr env cexpr >>= return . Cardinality
  HomologyGroupExpr hexpr -> evalHomologyGroupExpr env hexpr >>= return . HomologyGroup
  ChainExpr cexpr         -> evalChainExpr env cexpr >>= return . ChainValue

