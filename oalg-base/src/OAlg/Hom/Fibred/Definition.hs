
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Hom.Fibred.Definition
-- Description : definition of homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred.Definition
  (
    -- * Fibred
    HomFibred, FunctorialFibred

    -- * Duality
  , DualisableFibred
  , toDualStk, toDualRt
  )
  where

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Dualisable

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- HomFibred -

-- | homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @'HomFibred' __h__@, then for all @__x__@, @__y__@ and @h@ in
-- @__h x y__@ holds:
--
-- (1) @'root' '.' 'amap' h '.=.' 'rmap' h '.' 'root'@.
class ( Morphism h, Applicative h, ApplicativeRoot h
      , Transformable (ObjectClass h) Fbr
      ) => HomFibred h where


instance HomFibred h => HomFibred (Path h)
instance TransformableFbr s => HomFibred (HomEmpty s)

--------------------------------------------------------------------------------
-- DualisableFibred -

-- | duality according to @__o__@ on 'FibredOriented' structures.
--
-- __Properties__ Let @'DualisableFibred' __s o__@, then
-- for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'root' '.' 'toDualStk' q s '.=.' 'toDualRt' q s '.' 'root'@.
--
-- where @q@ is any proxy for @__o__@.
class (DualisableG s (->) o Id, DualisableG s (->) o Rt, Transformable s Fbr)
  => DualisableFibred s o

instance (TransformableType s, TransformableFbrOrt s, TransformableOp s) => DualisableFibred s Op

--------------------------------------------------------------------------------
-- toDualStk -

-- | the dual stalk ginven by @'DualisableFibred' __s o__@.
toDualStk :: DualisableFibred s o => q o -> Struct s x -> x -> o x
toDualStk _ s = fromIdG (toDualG' (d s) s) where
  d :: DualisableFibred s o => Struct s x -> DualityG s (->) o Id
  d _ = DualityG

--------------------------------------------------------------------------------
-- toDualRt -

toDualRt :: DualisableFibred s o => q o -> Struct s x -> Root x -> Root (o x)
toDualRt q s = fromRtG (toDualG' (d q s) s) where
  d :: DualisableFibred s o => q o -> Struct s x -> DualityG s (->) o Rt
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- HomDisj - HomFibred -

instance (HomFibred h, DualisableFibred s o) => HomFibred (HomDisj s o h)

--------------------------------------------------------------------------------
-- Functorialibred -

-- | functorial application of 'Fibred' homomorphisms.
type FunctorialFibred h = (HomFibred h, Functorial h, FunctorialRoot h)

