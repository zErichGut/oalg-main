
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homology.
module OAlg.Homology.Definition
  (
{-    
    -- * Homology
    Homology()
    
    -- * Chain Complex Free
  , ChainComplexFree()
-}
  ) where

import Control.Monad

import Data.Typeable
import Data.Foldable (toList)

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Free
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Matrix.Vector

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Limes.Definition
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free
import OAlg.Limes.KernelsAndCokernels

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex


import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality
import OAlg.Structure.Oriented
import OAlg.Structure.Distributive
import OAlg.Hom.Definition
import OAlg.Limes.Cone

--------------------------------------------------------------------------------
-- abgSomeFree -

abgSomeFree :: AbGroup -> Maybe (SomeFree AbHom)
abgSomeFree g | g == abg 0 ^ k = Just $ case someNatural k of SomeNatural k' -> SomeFree $ Free k' 
              | otherwise       = Nothing
  where k = lengthN g

--------------------------------------------------------------------------------
-- ChainComplexFree

data ChainComplexFree s n x where
  ChainComplexFree :: Typeable x
    => ChainComplex n (ChainOperator Z s)
    -> ConsecutiveZeroFree To n AbHom
    -> ChainComplexFree s n x

--------------------------------------------------------------------------------
-- chainComplexFree -

chainComplexFree :: Simplical s x
  => Regular -> Any n -> Complex x -> ChainComplexFree s n x
chainComplexFree r n c = ChainComplexFree cos (ccpOpsZSet cos) where
  cos = chainComplexOperators Struct r n c
  
  ccpOpsZSet ::Typeable s
    => ChainComplex n (ChainOperator Z s) -> ConsecutiveZeroFree To n AbHom
  ccpOpsZSet cos = ConsecutiveZeroFree cf fs where
    cf = cnzMapCov (homDisjOpDst FreeAbHom) $ ccpRepMatrix cos
    fs = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram cf 

chainComplexFree' :: Simplical s x
  => q s -> Regular -> Any n -> Complex x -> ChainComplexFree s n x
chainComplexFree' _ = chainComplexFree

--------------------------------------------------------------------------------
-- Homology -

-- | homology for the simplex type @__s__@ over vertices of type @__x__@.
data Homology s n x where
  Homology :: (Simplical s x, Attestable n)
    => N -- actual dimension
    -> ChainComplex n (ChainOperator Z s)
    -> VarianceFreeLiftable To n AbHom
    -> Homology s n x

--------------------------------------------------------------------------------
-- homology -

-- | the induced homology of a complex.
homology :: (Simplical s x, Attestable n) => Regular -> Any n -> Complex x -> Homology s n x
homology = error "nyi"

{-
homology r dMax c = case someNatural dMax of
  SomeNatural dMax' -> Homology 0 cos vfs where
    ChainComplexFree cos cf = chainComplexFree r dMax' c
    vfs = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree cf
{-
-- | the induced homology of a complex according to the proxy type.
homology' :: Simplical s x => q s -> Regular -> N -> Complex x -> Homology s x
homology' _ = homology

--------------------------------------------------------------------------------
-- hmgCards -

-- | the cardinalities of the simplex sets.
hmgCards :: Homology s x -> [N]
hmgCards (Homology _ cos _) = case cos of
  ConsecutiveZero d -> toList $ amap1 lengthN $ dgPoints d

--------------------------------------------------------------------------------
-- attest2 -

attest2 :: Attestable n => q n x -> Any n
attest2 _ = attest

--------------------------------------------------------------------------------
-- hmgRange -

-- | the range of the homology.
hmgRange :: Homology s x -> (N,N)
hmgRange (Homology i cos _) = (i,i + lengthN (attest2 cos))

--------------------------------------------------------------------------------
-- hmgIndex -

-- | the actual index.
hmgIndex :: Homology s x -> N
hmgIndex = fst . hmgRange

--------------------------------------------------------------------------------
-- hmgGroups -

-- | the homology groups.
hmgGroups :: Homology s x -> [AbGroup]
hmgGroups (Homology _ _ vfs) = toList $ dgPoints $ deviationsTo vfs

--------------------------------------------------------------------------------
-- hmgGroup -

-- | the homology group at the aktual index.
hmgGroup :: Homology s x -> AbGroup
hmgGroup (Homology _ _ vfs) = head $ dgPoints $ deviationsTo vfs

--------------------------------------------------------------------------------
-- EvalFailure -

-- | evaluation failures.
data EvalFailure
  = NoSuccesor
  | IndexOutOfRange N
  | EvalFailure String
  deriving (Show)

failure :: EvalFailure -> Eval x
failure = Left

--------------------------------------------------------------------------------
-- Eval -

-- | evaluation monad for homology.
type Eval x = Either EvalFailure x

--------------------------------------------------------------------------------
-- hmgSucc -

-- | increases the actual index by one.
hmgSucc :: Homology s x -> Eval (Homology s x)
hmgSucc (Homology i cos vfs) = case attest2 cos of
  W0   -> failure NoSuccesor
  SW n -> case ats n of Ats -> return $ Homology (succ i) (cnzTail cos) (vrcTail vfs) 
  
--------------------------------------------------------------------------------
-- hmgAt -

-- | sets the index to the given one. 
hmgAt :: N -> Homology s x -> Eval (Homology s x)
hmgAt i hg | l <= i && i <= h = at l i hg
           | otherwise        = failure $ IndexOutOfRange i
  where (l,h) = hmgRange hg
        at l i h | l == i    = return h
                 | otherwise = hmgSucc h >>= at (succ l) i
                  
--------------------------------------------------------------------------------
-- hmgSimplices -

-- | the set of simplices at the actual index, which form a base for the free abelian group of chains
-- of dimension given by the actual index.
hmgSimplices :: Homology s x -> Eval (Set (s x))
hmgSimplices h@(Homology _ cos _) = case cos of
  ConsecutiveZero cs         -> case cs of
    DiagramChainTo _ (d:|_)  -> case start d of
      SimplexSet ssx         -> case eqType h ssx of
        Just Refl            -> return ssx
        Nothing              -> failure $ EvalFailure "implementation error at: hmgSimplices"
  where
    eqType :: (Typeable x, Typeable y) => q x -> Set (s y) -> Maybe (x :~: y)
    eqType _ _ = eqT

-----------------------------------------------------------------------------------------
-- Chain -

-- | chain of the given simplex type over the given vertex type.
type Chain s x = ChainG Z s x

--------------------------------------------------------------------------------
-- abges -

-- | list of the canonical generators
abges :: AbGroup -> [AbElement]
abges g = [abge g (pred i) | i <- [1..lengthN g]] 

abeFreeFrom :: AbElement -> Slice From (Free N1) AbHom
abeFreeFrom (AbElement f) = f

--------------------------------------------------------------------------------
-- hmgToChain -

-- | the chain according to the actual simplex set and the given vector.
--
-- __Note__ The indices of the given vector which succed the cardinality of the given set,
-- will be troped.
hmgToChain :: Homology s x -> Vector Z -> Eval (Chain s x)
hmgToChain h@(Homology _ _ _) v = do
  ssx <- hmgSimplices h
  return (cfsssy ssx v)

--------------------------------------------------------------------------------
-- hmg -

-- | a base for the cycles at the actual index.
hmgCycles :: Homology s x -> Eval [Chain s x]
hmgCycles h@(Homology _ _ vfs)  = case vfs of
  VarianceG aCos ((aKer,_):|_) -> case universalCone aKer of
    ConicFreeTip _ aCn         -> sequence
                                $ amap1 (hmgToChain h . abhvecFree1 . (k*>). abeFreeFrom)
                                $ abges
                                $ start k
      where k = kernelFactor aCn


--------------------------------------------------------------------------------

c   = complex [Set [0..4]] :: Complex N
h   = homology' (Proxy :: Proxy Asc) Regular 5 c
-}


{-
(ChainComplexFree cos cf)
  = Homology cos (varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree cf)
-}
{-
--------------------------------------------------------------------------------
-- hmgTail -

hmgTail :: Typeable s => Homology s (n+1) x -> Homology s n x
hmgTail (Homology cos vf) = Homology (cnzTail cos) (vrcTail vf)

--------------------------------------------------------------------------------
-- hmgGroup -

hmgGroup :: Attestable n => Homology s n x -> AbGroup
hmgGroup = head . dgPoints . hmgGroups

--------------------------------------------------------------------------------
-- hmgChains -

-- hmgChains :: Homology n AbHom -> [Chain AbHom]

--------------------------------------------------------------------------------

c   = complex [Set [0..5]] :: Complex N
h   = homology $ chainComplexFree' (Proxy :: Proxy [])  Regular (attest :: Any N5) c


-}
