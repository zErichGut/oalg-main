
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

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Slice.Free
import OAlg.Entity.Sequence.Set

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

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

data Homology s x where
  Homology :: (Typeable x, Typeable s, Attestable n)
    => N -- actual dimension
    -> ChainComplex n (ChainOperator Z s)
    -> VarianceFreeLiftable To n AbHom
    -> Homology s x

--------------------------------------------------------------------------------
-- homology -

homology :: Simplical s x => Regular -> N -> Complex x -> Homology s x
homology r dMax c = case someNatural dMax of
  SomeNatural dMax' -> Homology 0 cos vfs where
    ChainComplexFree cos cf = chainComplexFree r dMax' c
    vfs = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree cf

homology' :: Simplical s x => q s -> Regular -> N -> Complex x -> Homology s x
homology' _ = homology

--------------------------------------------------------------------------------
-- hmgRange -

hmgRange :: Homology s x -> (N,N)
hmgRange (Homology i cos _) = (i,i + lengthN (d cos)) where
  d :: Attestable n => q n x -> Any n
  d _ = attest

--------------------------------------------------------------------------------
-- hmgIndex -

hmgIndex :: Homology s x -> N
hmgIndex = fst . hmgRange

--------------------------------------------------------------------------------
-- hmgGroups -

hmgGroups :: Homology s x -> [AbGroup]
hmgGroups (Homology _ _ vfs) = toList $ dgPoints $ deviationsTo vfs

--------------------------------------------------------------------------------
-- hmgGroup -

-- | the homology group at the aktual index.
hmgGroup :: Homology s x -> AbGroup
hmgGroup (Homology _ _ vfs) = head $ dgPoints $ deviationsTo vfs

--------------------------------------------------------------------------------
-- EvalFailure -

data EvalFailure
  = NoSuccesor
  | EvalFailure String
  deriving (Show)

failure :: EvalFailure -> Eval x
failure = Left

--------------------------------------------------------------------------------
-- Eval -

type Eval x = Either EvalFailure x

--------------------------------------------------------------------------------
-- hmgSucc -

hmgSucc :: Homology s x -> Eval (Homology s x)
hmgSucc (Homology i cos vfs) = case d cos of
  W0   -> failure NoSuccesor
  SW n -> case ats n of Ats -> return $ Homology (succ i) (cnzTail cos) (vrcTail vfs) 
  where
    d :: Attestable n => q n x -> Any n
    d _ = attest
  

--------------------------------------------------------------------------------
-- hmgSimplices -

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


--------------------------------------------------------------------------------

c   = complex [Set [0..2]] :: Complex N
h   = homology' (Proxy :: Proxy Set) Regular 5 c



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

-----------------------------------------------------------------------------------------
-- Chain -

type Chain x = ChainG Z Set x

--------------------------------------------------------------------------------
-- hmgChains -

-- hmgChains :: Homology n AbHom -> [Chain AbHom]

--------------------------------------------------------------------------------

c   = complex [Set [0..5]] :: Complex N
h   = homology $ chainComplexFree' (Proxy :: Proxy [])  Regular (attest :: Any N5) c


-}
