
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- | Minima and Maxima,
-- i.e. limits of 'Chain'-diagrams.
module OAlg.Limes.MinimaAndMaxima
  (
    -- * Minima
    Minima, Minimum, MinimumCone, MinimumDiagram
  , minimaTo, minimaFrom

    -- * Maxima
  , Maxima, Maximum, MaximumCone, MaximumDiagram
  , maximaTo, maximaTo', maximaFrom, maximaFrom'

    -- * Duality
  , maxLimitsDualityTo, maxLimitsDualityFrom

  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.Diagram

import OAlg.Structure.Multiplicative

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits


--------------------------------------------------------------------------------
-- Minima -

type MinimumDiagram t n         = Diagram (Chain t) (n+1) n
type MinimumCone t n            = Cone Mlt Projective (Chain t) (n+1) n
type Minimum t n                = Limes Mlt Projective (Chain t) (n+1) n
type Minima t n                 = Limits Mlt Projective (Chain t) (n+1) n

--------------------------------------------------------------------------------
-- minima -

minimaTo :: Multiplicative a => Minima To n a
minimaTo = Limits lMin where
  lMin :: Multiplicative a => MinimumDiagram To n a -> Minimum To n a
  lMin d = LimesProjective l u where
    l = cnPrjChainTo (FactorChain (one (chnToStart d)) d)
    u c = f where FactorChain f _ = cnPrjChainToInv c

minimaFrom :: Multiplicative a => Minima From n a
minimaFrom = Limits lMin where
  lMin :: Multiplicative a => MinimumDiagram From n a -> Minimum From n a
  lMin d = LimesProjective l u where
    l = cnPrjChainFrom (FactorChain (one (chnFromStart d)) d)
    u c = f where FactorChain f _ = cnPrjChainFromInv c

--------------------------------------------------------------------------------
-- Maxima -

type MaximumDiagram t n         = Diagram (Chain t) (n+1) n
type MaximumCone t n            = Cone Mlt Injective (Chain t) (n+1) n
type Maximum t n                = Limes Mlt Injective (Chain t) (n+1) n
type Maxima t n                 = Limits Mlt Injective (Chain t) (n+1) n

--------------------------------------------------------------------------------
-- Duality - Max -

maxLimitsDualityTo :: Multiplicative a => LimitsDuality Mlt (Maxima To n) (Minima From n) a
maxLimitsDualityTo = LimitsDuality ConeStructMlt Refl Refl Refl Refl

maxLimitsDualityFrom :: Multiplicative a
  => LimitsDuality Mlt (Maxima From n) (Minima To n) a
maxLimitsDualityFrom = LimitsDuality ConeStructMlt Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- maxima -

maximaTo :: Multiplicative a => Maxima To n a
maximaTo = lmsFromOp maxLimitsDualityTo minimaFrom

maximaFrom :: Multiplicative a => Maxima From n a
maximaFrom = lmsFromOp maxLimitsDualityFrom minimaTo

maximaTo' :: Multiplicative a => p n -> f a -> Maxima To n a
maximaTo' _ _ = maximaTo

maximaFrom' :: Multiplicative a => p n -> f a -> Maxima From n a
maximaFrom' _ _ = maximaFrom
