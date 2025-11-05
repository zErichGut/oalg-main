
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

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
  , limesCone, limitsCone

    -- * Constructions
  , lmsMltPrjOrnt, lmsMltInjOrnt
  ) where

import OAlg.Prelude

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
-- limesCone -

-- | the underlying limes according to 'Cone' , given by a diagrammatic object of @__d t n m x__@.
limesCone :: Conic c => LimitsG c s p d t n m x -> d t n m x -> LimesG Cone s p d t n m x
limesCone lG d = case limes lG d of
  LimesProjective cCn cUniv -> LimesProjective (cone cCn) cUniv
  LimesInjective cCn cUniv  -> LimesInjective (cone cCn) cUniv

--------------------------------------------------------------------------------
-- limitsCone -

-- | the underlying limits according to 'Cone'.
limitsCone :: Conic c => LimitsG c s p d t n m x -> LimitsG Cone s p d t n m x
limitsCone = LimitsG . limesCone

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

