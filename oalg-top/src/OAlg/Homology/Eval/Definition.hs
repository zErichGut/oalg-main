
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Eval.Definition
-- Description : evaluations for homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- evaluations for homology.
module OAlg.Homology.Eval.Definition
  (
  ) where

import Control.Monad 

import Data.Kind
import Data.Array
import Data.List as L (zip,(++))
import qualified Data.Map as M

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
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sum
-- import OAlg.Entity.Slice.Free
import OAlg.Entity.Matrix

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
import OAlg.Homology.Eval.Core

import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
-- ChainType -

data ChainType = Chain | Cycle | Homology
  deriving (Show,Eq,Ord,Enum,Bounded,Ix)

--------------------------------------------------------------------------------
-- ChainValue -

type ChainValue s x = ChainG Z s x

--------------------------------------------------------------------------------
-- ChainList -

type ChainList s x = Array N (ChainValue s x)

--------------------------------------------------------------------------------
-- ChainIndex -

data ChainIndex = ChainIndex ChainType N deriving (Show,Eq,Ord)

instance Validable ChainIndex where
  valid (ChainIndex t n) = valid n && case t of
    Chain -> SValid
    _     -> SValid

--------------------------------------------------------------------------------
-- VarBind -

newtype VarBind s x = VarBind (M.Map (N,String) (ChainValue s x))

--------------------------------------------------------------------------------
-- SomeChainComplex -

-- | ignoring the 'ChainComplexType'.
data SomeChainComplex r s n x where
  SomeChainComplex ::  ChainComplex t r s n x -> SomeChainComplex r s n x

--------------------------------------------------------------------------------
-- Env -

data Env t s n x where
  Env :: (Simplical s x, Attestable n)
    => { envMaxDim       :: N
       , envChainComplex :: ChainComplex t Z s n x
       , envHomology     :: Homology n
       , envAt           :: Array N (SomeChainComplex Z s N0 x, Homology N0)
       , envChains       :: Array N (Array ChainType (ChainList s x))
       }
    -> Env t s n x

--------------------------------------------------------------------------------
-- env -

env :: (Simplical s x, Attestable n) => ChainComplexType t -> Any n -> Complex x -> Env t s n x
env t n c = case ats n of
  Ats -> Env { envMaxDim       = dm
             , envChainComplex = ccx
             , envHomology     = hmg
             , envAt           = at
             , envChains       = fmap chns at
             } where
    dm  = lengthN n
    ccx = chainComplex t n c
    hmg = homology ccx
    at  = array (0,dm) $ ascsAt n 0 ccx hmg

    ascsAt :: Simplical s x
      => Any n -> N
      -> ChainComplex t Z s n x -> Homology n
      -> [(N,(SomeChainComplex Z s N0 x,Homology N0))]
    ascsAt n i cc hm = (i,(SomeChainComplex $ ccxHead cc,vrcHead hm)) : case n of
      W0    -> []
      SW n' -> ascsAt n' (succ i) (ccxTail cc) (vrcTail hm)

    chns :: Simplical s x
      => (SomeChainComplex Z s N0 x,Homology N0) -> Array ChainType (ChainList s x)
    chns ch@(SomeChainComplex ccx,_)
      = array (Chain,Homology) [ (Chain,chnsChain ccx)
                               , (Cycle,chnsCycle ch)
                               , (Homology,chnsCls ch)
                               ]

    chnsChain :: Simplical s x => ChainComplex t Z s N0 x -> ChainList s x
    chnsChain (ChainComplex _ (DiagramChainTo _ (d:|_)))
      = array rng $ ([0..] `L.zip` ((\(Set sxs) -> amap1 ch sxs) ssxs)) where
      
      ssxs = start d
      rng  = case lengthN ssxs of
               0 -> (1,0)
               l -> (0,pred l)


    -- mapping the elements to chain values.
    toChnVls :: Simplical s x => SomeChainComplex Z s N0 x -> [AbElement] -> ChainList s x
    toChnVls (SomeChainComplex ccx) es
      = array rng $ L.zip [0..] $ amap1 (cfsssy ssx . abgevec) $ es where

      ChainComplex _ (DiagramChainTo _ (d:|_)) = ccx
      ssx = start d
      rng = case lengthN es of
        0 -> (1,0)
        l -> (0,pred l)

    chnsCycle :: Simplical s x => (SomeChainComplex Z s N0 x,Homology N0) -> ChainList s x
    chnsCycle (sccx,hmg) = toChnVls sccx $ hmgCycles hmg

    chnsCls :: Simplical s x => (SomeChainComplex Z s N0 x,Homology N0) -> ChainList s x
    chnsCls (sccx,hmg) = toChnVls sccx $ hmgClassGenerators hmg

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
evalAt env at
  | envMaxDim env < at = failure $ IndexOutOfRange at
  | otherwise          = return $ (envAt env ! at)

--------------------------------------------------------------------------------
-- evalToAbElement -

-- | converting to the corresponding abelien element.
evalToAbElement :: Env t s n x -> N -> ChainValue s x -> Eval AbElement
evalToAbElement env@Env{} at ch = do
  SomeChainComplex ccx <- evalAt env at >>= return . fst
  case ccx of ChainComplex _ (DiagramChainTo _ (d:|_)) -> toAbElm (start d) ch

  where
    toAbElm :: Simplical s x => Set (s x) -> ChainValue s x -> Eval AbElement
    toAbElm ssx ch
      | ch' /= ch = failure $ NotEligible "evalToAbElement"
      | otherwise = return $ AbElement $ vecabhFree1 n cfs
      where ch' = cfsssy ssx cfs
            cfs = ssycfs ssx ch
            n   = lengthN ssx
  
--------------------------------------------------------------------------------
-- evalFromAbElement -

-- | converting from the corresponding abelien element.
evalFromAbElement :: Env t s n x -> N -> AbElement -> Eval (ChainValue s x)
evalFromAbElement = error "nyi"

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
-- evalChainValue -

evalChainValueAtEnv :: Env t s n x -> N -> ChainType -> N -> Eval (ChainValue s x)
evalChainValueAtEnv env@Env{} i t j = do
  chsAt <- evalElmAt (envChains env) i (AtOutOfRange i)
  chsTp <- evalElmAt chsAt t (EvalFailure ("unsupported chain type: " L.++ show t))
  evalElmAt chsTp j (IndexOutOfRange j)

--------------------------------------------------------------------------------
-- evalChainValue -

evalChainValueAtSmf :: Env t s n x -> VarBind s x
  -> N -> SumForm Z (R ChainIndex) -> Eval (ChainValue s x)
evalChainValueAtSmf env@Env{} vrs at sf
  | envMaxDim env < at = failure $ AtOutOfRange at
  | otherwise          = evl env vrs at (reduce sf) >>= return . SumSymbol . make where
  
  evl env vrs at sf = case sf of
    Zero ()  -> return $ Zero ()
    z :! sf' -> evl env vrs at sf' >>= return . (z:!)
    a :+ b   -> do
      a' <- evl env vrs at a
      b' <- evl env vrs at b
      return (a' :+ b')
    S (R (ChainIndex t i)) -> do
      SumSymbol sx <- evalChainValueAtEnv env at t i
      return $ form sx


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
  | CardSimplexSetAtExpr

--------------------------------------------------------------------------------
-- HomologyGroupExpression -

-- | expression to evaluate values of type t'HomologyGroup'.
data HomologyGroupExpression
  = HomologyGroupAllExpr
  | HomologyGroupAtExpr

--------------------------------------------------------------------------------
-- ChainListAtExpression -

data ChainExpression
  = ChainListAtExpr ChainType
  | ChainValueAtExpr ChainValueAtExpression
  | ChainApplicationAtExpr ChainOperatorType ChainValueAtExpression

--------------------------------------------------------------------------------
-- ChainExpression -

data ChainValueAtExpression = ChainSumFormAt (SumForm Z (R ChainIndex))

--------------------------------------------------------------------------------
-- ChainOperatorType -

data ChainOperatorType
  = HomologyClass
  
--------------------------------------------------------------------------------
-- Value -

data Value (s :: Type -> Type) x
  = MaximalDimension N
  | Cardinality (Cardinality s x)
  | HomologyGroup (HomologyGroup s x)
  | ChainList (ChainList s x)
  | ChainValue (ChainValue s x)
  | HomologyClassValue AbElement
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

evalCardinalityExpr :: Env t s n x -> N -> CardinalityExpression -> Eval (Cardinality s x)
evalCardinalityExpr env@Env{} at cexpr = case cexpr of
  CardSimplexSetAllExpr  -> return $ SimplexSetCardinalities $ evalCardSmplSetAll env
  CardSimplexSetAtExpr -> evalCardSmplSetAt env at >>= return . SimplexSetCardinalities 

--------------------------------------------------------------------------------
-- evalHomologyGroupExpr -

evalHomologyGroupExpr :: Env t s n x -> N -> HomologyGroupExpression -> Eval (HomologyGroup s x)
evalHomologyGroupExpr env@Env{} at hexpr = case hexpr of
  HomologyGroupAllExpr  -> return $ HomologyGroups $ evalHomologyGroups env
  HomologyGroupAtExpr   -> evalHomologyGroupAt env at >>= return . HomologyGroups

--------------------------------------------------------------------------------
-- evalChainListAt -

evalChainListAt :: Env t s n x -> N -> ChainType -> Eval (ChainList s x)
evalChainListAt env at t = do
  chsAt <- evalElmAt (envChains env) at (AtOutOfRange at)
  evalElmAt chsAt t (EvalFailure ("unsupported chain type: " L.++ show t))

--------------------------------------------------------------------------------
-- evalChainValueAt -

evalChainValueAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval (ChainValue s x)
evalChainValueAt env vrs at (ChainSumFormAt sf) = evalChainValueAtSmf env vrs at sf

--------------------------------------------------------------------------------
-- evalHomologyClassAt -

evalHomologyClassAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval AbElement
evalHomologyClassAt env vrs at vexpr = do
  ch <- evalChainValueAt env vrs at vexpr
  e  <- evalToAbElement env at ch
  h  <- evalAt env at >>= return . snd
  homologyClass h e

--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> VarBind s x -> N -> Expression -> Eval (Value s x)
eval env vrs at expr        = case expr of
  MaxDimExpr               -> return $ MaximalDimension $ envMaxDim env
  CardinalityExpr cexpr    -> evalCardinalityExpr env at cexpr >>= return . Cardinality
  HomologyGroupExpr hexpr  -> evalHomologyGroupExpr env at hexpr >>= return . HomologyGroup
  ChainExpr cexpr          -> case cexpr of
    ChainListAtExpr t      -> evalChainListAt env at t >>= return . ChainList
    ChainValueAtExpr vexpr -> evalChainValueAt env vrs at vexpr >>= return . ChainValue
    ChainApplicationAtExpr HomologyClass vexpr
                           -> evalHomologyClassAt env vrs at vexpr >>= return . HomologyClassValue

vrs = VarBind $ M.empty

hmgs  = HomologyGroupExpr HomologyGroupAllExpr
hmg   = HomologyGroupExpr HomologyGroupAtExpr

crds  = CardinalityExpr CardSimplexSetAllExpr
crd   = CardinalityExpr CardSimplexSetAtExpr

chsAt = ChainExpr (ChainListAtExpr Chain)
chAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Chain

cysAt = ChainExpr (ChainListAtExpr Cycle)
cyAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Cycle

hgwAt = ChainExpr (ChainListAtExpr Homology)
hgAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Homology

hcAt t i = ChainExpr (ChainApplicationAtExpr HomologyClass (ChainSumFormAt $ S $ R $ ChainIndex t i))
