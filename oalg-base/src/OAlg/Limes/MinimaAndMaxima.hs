
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.MinimaAndMaxima
-- Description : minima and maxima
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- minima and maxima within a 'Multiplicative' structure, i.e. limits of @'Diagram' ('Chain' __t__)@.
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
import OAlg.Limes.OpDuality
import OAlg.Limes.Definition
import OAlg.Limes.Limits


--------------------------------------------------------------------------------
-- Minima -

-- | 'Diagram' for a minimum.
type MinimumDiagram t n = Diagram (Chain t) (n+1) n

-- | 'Cone' for a minimum.
type MinimumCone t n = Cone Mlt Projective (Chain t) (n+1) n

-- | minimum as 'Limes'.
type Minimum t n = Limes Mlt Projective (Chain t) (n+1) n

-- | minima for a 'Multiplicative' structure.
type Minima t n = Limits Mlt Projective (Chain t) (n+1) n

--------------------------------------------------------------------------------
-- minima -

-- | minima according to @'Chain' 'To'@.
minimaTo :: Multiplicative a => Minima To n a
minimaTo = Limits lMin where
  lMin :: Multiplicative a => MinimumDiagram To n a -> Minimum To n a
  lMin d = LimesProjective l u where
    l = cnPrjChainTo (FactorChain (one (chnToStart d)) d)
    u c = f where FactorChain f _ = cnPrjChainToInv c

-- | minima according to @'Chain' 'From'@.
minimaFrom :: Multiplicative a => Minima From n a
minimaFrom = Limits lMin where
  lMin :: Multiplicative a => MinimumDiagram From n a -> Minimum From n a
  lMin d = LimesProjective l u where
    l = cnPrjChainFrom (FactorChain (one (chnFromStart d)) d)
    u c = f where FactorChain f _ = cnPrjChainFromInv c

--------------------------------------------------------------------------------
-- Maxima -

-- | 'Diagram' for a maximum.
type MaximumDiagram t n = Diagram (Chain t) (n+1) n

-- | 'Cone' for a maximum.
type MaximumCone t n = Cone Mlt Injective (Chain t) (n+1) n

-- | maximum as a 'Limes'.
type Maximum t n = Limes Mlt Injective (Chain t) (n+1) n

-- | maxima for a 'Multiplicative' structure.
type Maxima t n = Limits Mlt Injective (Chain t) (n+1) n

--------------------------------------------------------------------------------
-- Duality - Max -

-- | duality between @'Maxima' 'To'@ and @'Minima' 'From'@.
maxLimitsDualityTo :: OpDuality Limits Mlt (Maxima To n) (Minima From n)
maxLimitsDualityTo = OpDuality Refl Refl Refl Refl

-- | duality between @'Maxima' 'From'@ and @'Minima' 'To'@.
maxLimitsDualityFrom :: OpDuality Limits Mlt (Maxima From n) (Minima To n)
maxLimitsDualityFrom = OpDuality Refl Refl Refl Refl

--------------------------------------------------------------------------------
-- maxima -

-- | maxima according to @'Chain' 'To'@.
maximaTo :: Multiplicative a => Maxima To n a
maximaTo = lmsFromOp ConeStructMlt maxLimitsDualityTo minimaFrom

-- | maxima according to @'Chain' 'From'@.
maximaFrom :: Multiplicative a => Maxima From n a
maximaFrom = lmsFromOp ConeStructMlt maxLimitsDualityFrom minimaTo

-- | maxima according to @'Chain' 'To'@ given by two proxy types.
maximaTo' :: Multiplicative a => p n -> f a -> Maxima To n a
maximaTo' _ _ = maximaTo

-- | maxima according to @'Chain' 'From'@ given by two proxy types.
maximaFrom' :: Multiplicative a => p n -> f a -> Maxima From n a
maximaFrom' _ _ = maximaFrom
