
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Limes.Limits.Core
-- Description : basic definition for limits of diagrammatic objects.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basic definition for a 'LimesG' of diagrammatic object.
module OAlg.Limes.Limits.Core
  (
    -- * Limits
    limes, LimitsG(..), Limits

    -- * Constructions
  , lmsMltPrjOrnt, lmsMltInjOrnt

{-
    -- * Mapping
  , lmsMapS, lmsMapCov, lmsMapCnt

    -- * Proposition
  , prpLimitsG
-}
  ) where

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Variant
import OAlg.Data.Either

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Entity.Diagram

import OAlg.Limes.Cone
import OAlg.Limes.Definition

--------------------------------------------------------------------------------
-- LimitsG -

-- | limes of a diagrammatic object, i.e. assigning to each diagrammatic object @d@ a limes over the
-- @d@.
--
-- __Property__ Let @l@ be in @'LimitsG' __c s p d t n m x__@ for a @'Conic' __c__@ and a
-- @'Diagrammatic' __d__@, then holds:
--
-- (1) @'diagram' '.' 'cone' '.' 'universalCone' '.' 'limes' l '.=.' 'diagram'@.
newtype LimitsG c s p d t n m x = LimitsG (d t n m x -> LimesG c s p d t n m x)

--------------------------------------------------------------------------------
-- Limits -

-- | limits for 'Cone's over 'Diagram's.
type Limits s p = LimitsG Cone s p Diagram

--------------------------------------------------------------------------------
-- limes -

-- | the limes over the given diagram.
limes :: LimitsG c s p d t n m x -> d t n m x -> LimesG c s p d t n m x
limes (LimitsG l) = l

--------------------------------------------------------------------------------
-- lmsMltPrjOrnt -

-- | projective limits for 'Multiplicative' structures over @'Orientation' __p__@ .
lmsMltPrjOrnt :: Entity p => p -> Limits Mlt Projective t n m (Orientation p)
lmsMltPrjOrnt = LimitsG . lmMltPrjOrnt

--------------------------------------------------------------------------------
-- lmsMltInjOrnt -

-- | injective limits for 'Multiplicative' structures over @'Orientation' __p__@.
lmsMltInjOrnt :: Entity p => p -> Limits Mlt Injective t n m (Orientation p)
lmsMltInjOrnt = LimitsG . lmMltInjOrnt  

{-
--------------------------------------------------------------------------------
-- LimitsG - Dual -

type instance Dual1 (LimitsG c s p d t n m) = LimitsG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmsMapCov -

lmsMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> LimitsG c s p d t n m y
lmsMapCov i@(Covariant2 (Inv2 _ f)) (LimitsG u) = LimitsG u' where
  u' d' = lmMapCov i (u d) where
    SDualBi (Right1 (DiagramG d)) = amapF f (SDualBi (Right1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapCnt -

lmsMapCnt :: NaturalConic h c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimitsG c s p d t n m x -> Dual1 (LimitsG c s p d t n m) y
lmsMapCnt i@(Contravariant2 (Inv2 _ f)) (LimitsG u) = LimitsG u' where
  u' d' = lmMapCnt i (u d) where
    SDualBi (Right1 (DiagramG d)) = amapF f (SDualBi (Left1 (DiagramG d'))) 

--------------------------------------------------------------------------------
-- lmsMapS -

lmsMapS ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Inv2 h x y -> SDualBi (LimitsG c s p d t n m) x -> SDualBi (LimitsG c s p d t n m) y
lmsMapS = vmapBi lmsMapCov lmsMapCov lmsMapCnt lmsMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi h c s p d t n m
  => ApplicativeG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmsMapS

instance NaturalConicBi h c s p d t n m
  => FunctorialG (SDualBi (LimitsG c s p d t n m)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- prpLimitsG -

-- | validity according to 'LimitsG'.
prpLimitsG ::
  ( Conic c
  , Diagrammatic d
  , Entity (d t n m x)
  , Entity x
  )
  => XEligibleCone c s p d t n m x
  -> XEligibleConeFactor c s p d t n m x
  -> X (d t n m x)
  -> LimitsG c s p d t n m x
  -> Statement
prpLimitsG xec xef xd l = Prp "LimitsG" :<=>: Forall xd (prpLimes xec xef . limes l)

--------------------------------------------------------------------------------
-- LimitsG - Validable -

instance
  ( Conic c
  , Diagrammatic d
  , XStandardEligibleCone c s p d t n m x
  , XStandardEligibleConeFactor c s p d t n m x
  , XStandard (d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => Validable (LimitsG c s p d t n m x) where
  valid = prpLimitsG xStandardEligibleCone xStandardEligibleConeFactor xStandard
-}

