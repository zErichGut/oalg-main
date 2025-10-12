
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
import OAlg.Data.Reducible
import OAlg.Data.Constructable

import OAlg.Structure.Oriented
-- import OAlg.Structure.Distributive
-- import OAlg.Structure.Exponential

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural hiding (S)
import OAlg.Entity.FinList as F
import OAlg.Entity.Sum
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
  | NotSupportedChainType String
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
-- evalElmAt -

evalElmAt :: Ix i => Array i x -> i -> EvalFailure -> Eval x
evalElmAt xs i f = if (bounds xs `inRange` i) then return (xs ! i) else failure f

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
-- ChainList -

type ChainList s x = Array N (ChainG Z s x)

--------------------------------------------------------------------------------
-- evalChainBaseAt -

evalChainBaseAt :: Env t s n x -> N -> Eval (ChainList s x)
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
-- evalChainListsAt -

evalChainListsAt :: Env t s n x -> N -> Eval (Array ChainType (ChainList s x))
evalChainListsAt env i = do
  bs <- evalChainBaseAt env i
  return $ array (Chain,Chain) [(Chain,bs)]

--------------------------------------------------------------------------------
-- ChainValue -

type ChainValue s x = ChainG Z s x

--------------------------------------------------------------------------------
-- evalChainValue -

evalChainValue :: Env t s n x -> Array ChainType (ChainList s x)
  -> SumForm Z (R ChainIndex) -> Eval (ChainValue s x)
evalChainValue env@Env{} chs sf = evl env chs (reduce sf) >>= return . SumSymbol . make where
  evl env chs sf = case sf of
    Zero ()  -> return $ Zero ()
    z :! sf' -> evl env chs sf' >>= return . (z:!)
    a :+ b   -> do
      a' <- evl env chs a
      b' <- evl env chs b
      return (a' :+ b')
    S (R (ChainIndex t i)) -> do
      cl           <- evalElmAt chs t (NotSupportedChainType $ show t)
      SumSymbol sx <- evalElmAt cl i (IndexOutOfRange i)
      return $ form sx

{-      
      cl <- when (bounds chs `inRange` t) (return (chs ! t))
                                          
      error "nyi"
-}          

--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression
  = MaxDimExpr -- ^ the maximal dimension
  | CardinalityExpr  CardinalityExpression -- ^ cardinality.
  | HomologyGroupExpr HomologyGroupExpression
  | ChainListAtExpr ChainListAtExpression
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
-- ChainListAtExpression -

data ChainListAtExpression
  = ChainBaseAtExpr N

--------------------------------------------------------------------------------
-- ChainExpression -

data ChainExpression
  = ChainSumForm N (SumForm Z (R ChainIndex))

--------------------------------------------------------------------------------
-- ChainIndex -

data ChainIndex = ChainIndex ChainType N deriving (Show,Eq,Ord)

instance Validable ChainIndex where
  valid (ChainIndex t n) = valid n && case t of
    Chain -> SValid
    _     -> SValid

--------------------------------------------------------------------------------
-- ChainType -

data ChainType = Chain | Cycle | Boundary | Homology
  deriving (Show,Eq,Ord,Enum,Bounded,Ix)

--------------------------------------------------------------------------------
-- Value -

data Value (s :: Type -> Type) x
  = MaximalDimension N
  | Cardinality (Cardinality s x)
  | HomologyGroup (HomologyGroup s x)
  | ChainList (ChainList s x)
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
-- evalChainListAtExpr -

evalChainListAtExpr :: Env t s n x -> ChainListAtExpression -> Eval (ChainList s x)
evalChainListAtExpr env cexpr = case cexpr of
  ChainBaseAtExpr i -> evalChainBaseAt env i

--------------------------------------------------------------------------------
-- evalChainExpr -

evalChainExpr :: Env t s n x -> ChainExpression -> Eval (ChainValue s x)
evalChainExpr env cexpr = case cexpr of
  ChainSumForm n sf -> do
    chs <- evalChainListsAt env n
    evalChainValue env chs sf

--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> Expression -> Eval (Value s x)
eval env expr = case expr of
  MaxDimExpr              -> return $ MaximalDimension $ evalMaxDim env
  CardinalityExpr cexpr   -> evalCardinalityExpr env cexpr >>= return . Cardinality
  HomologyGroupExpr hexpr -> evalHomologyGroupExpr env hexpr >>= return . HomologyGroup
  ChainListAtExpr cexpr   -> evalChainListAtExpr env cexpr >>= return . ChainList
  ChainExpr cexpr         -> evalChainExpr env cexpr >>= return . ChainValue

