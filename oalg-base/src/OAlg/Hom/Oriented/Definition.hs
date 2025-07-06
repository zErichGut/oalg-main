
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Hom.Oriented.Definition
-- Description : definition of homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Definition
  (
    -- * Disjunctive
    HomDisjunctiveOriented
  , omapDisj

    -- * Covariant
  , HomOriented

    -- * Dualisable
  , DualisableOriented
  , toDualArw, toDualPnt
  
    -- * Applicative
  , FunctorialOriented

  , module V
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Variant as V

import OAlg.Structure.Oriented.Definition hiding (Path(..))

import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- HomOriented -

-- | covariant homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @__h__@ be an instance of 'HomOriented', then
-- for all  @__a__@, @__b__@ and @h@ in @__h a b__@ holds:
--
-- (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
-- (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      ) => HomOriented h where

instance HomOriented h => HomOriented (Path h)
instance TransformableOrt s => HomOriented (IdHom s)

--------------------------------------------------------------------------------
-- HomDisjunctiveOriented -

-- | disjunctive homomorphism between 'Oriented' structures.
--
-- __Properties__ Let @'HomDisjunctiveOriented' __h__@, then
-- for all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
--     (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
-- (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--     (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--     (2) @'end' ',' 'amap' h '.=.' 'pmap' h '.' 'start'@.
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      , Disjunctive2 h
      )
  => HomDisjunctiveOriented h

instance TransformableOrt s => HomDisjunctiveOriented (IdHom s)

--------------------------------------------------------------------------------
-- FunctorialOriented -

-- | helper class to avoid undecidable instances.
class (CategoryDisjunctive h, HomDisjunctiveOriented h, Functorial h, FunctorialPoint h)
  => FunctorialOriented h 

--------------------------------------------------------------------------------
-- DualisableOriented -

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'DualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG Ort (->) o Id, DualisableG Ort (->) o Pnt
      , TransformableG o s s, Transformable s Ort
      )
  => DualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => DualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualArw :: DualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw q s = fromIdG (toDualG' (d q s) (tauOrt s)) where
  d :: DualisableOriented s o => q o -> Struct s x -> DualityG Ort (->) o Id
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualPnt :: DualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) (tauOrt s)) where
  d :: DualisableOriented s o => q o -> Struct s x -> DualityG Ort (->) o Pnt
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- omapDisj -

-- | induced application respecting the variant.
omapDisj :: (ApplicativePoint h, Disjunctive2 h)
  => h x y -> Orientation (Point x) -> Orientation (Point y)
omapDisj h = case variant2 h of
  Covariant     -> omap h
  Contravariant -> opposite . omap h

