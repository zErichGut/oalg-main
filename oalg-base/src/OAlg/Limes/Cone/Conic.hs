
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.Conic
-- Description : objects with a naturally underlying cone.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- objects with a naturally underlying cone.
module OAlg.Limes.Cone.Conic
  (
    -- * Conic
    Conic(..), ConeG(..)

    -- * Natural
  , NaturalConic, NaturalConicDual1
  , NaturalConicBi

  , NaturalConicSDualisable
    
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.NaturalTransformable

import OAlg.Data.Variant
import OAlg.Data.Either

import OAlg.Entity.Diagram
import OAlg.Entity.Natural

import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- Conic -

-- | object @__c__@ having an underlying 'Cone'.
class Conic c where
  cone :: c s p d t n m x -> Cone s p d t n m x

instance Conic Cone where cone = id

--------------------------------------------------------------------------------
-- ConeG -

-- | wrapper for 'Conic'-objects.
newtype ConeG (c :: Type -> Perspective
                 -> (DiagramType -> N' -> N' -> Type -> Type)
                 -> DiagramType -> N' -> N'
                 -> Type
                 -> Type
              ) s p d t n m x
  = ConeG (c s p d t n m x)
  deriving (Show,Eq)

type instance Dual1 (ConeG c s p d t n m) = ConeG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- cncGMap -

-- | the induced mapping.
cncGMap :: (c s p d t n m x -> c s p d t n m y) -> ConeG c s p d t n m x -> ConeG c s p d t n m y
cncGMap f (ConeG c) = ConeG (f c)

--------------------------------------------------------------------------------
-- croh -

-- | the underlying cone.
croh :: Conic c => ConeG c s p d t n m x -> Cone s p d t n m x
croh (ConeG c) = cone c

instance Conic c => Natural r (->) (ConeG c s p d t n m) (Cone s p d t n m) where
  roh _ = croh

--------------------------------------------------------------------------------
-- NaturalConic -

-- | natural transformation for 'Conic' objects.
--
-- __Property__ Let @'NaturalConic' __h c s p d t n m__@ and @'Hom' __s h__@ where @__s__@ is either
-- 'Mlt' or 'Dst', then for all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) @'amapG' h '.=. 'cnMap' h@,
--
-- __Note__ We haven't added the constraint @'Hom' __s h__@ to this class declaration because
-- this will not pass the type checker.
class
  ( Conic c
  , NaturalDiagrammatic h d t n m
  , NaturalTransformable h (->) (ConeG c s p d t n m) (Cone s p d t n m)
  )
  => NaturalConic h c s p d t n m

--------------------------------------------------------------------------------
-- prpNaturalConic -

-- | validity according to 'NaturalConic'.
prpNaturalConic ::
  ( Hom s h
  , NaturalConic h c s p d t n m
  , Show (d t n m x), Show2 h
  , Eq (d t n m y)
  )
  => q h c s p d t n m
  -> h x y -> Cone s p d t n m x -> Statement
prpNaturalConic _ h c = Prp "NaturalConic" :<=>:
  (amapG h c == cnMap h c) :?> Params ["h":=show2 h,"c":= show c]

--------------------------------------------------------------------------------
-- NaturalConicDual1 -

-- | helper class to avoid undecidable instances.
class NaturalConic h c s (Dual p) d (Dual t) n m => NaturalConicDual1 h c s p d t n m

--------------------------------------------------------------------------------
-- NaturalConicBi -

-- | constrains for conic objects @__c__@ which are bi-natural conic.
type NaturalConicBi h c s p d t n m
  = ( NaturalConic h c s p d t n m
    , NaturalConicDual1 h c s p d t n m
    )

--------------------------------------------------------------------------------
-- DualisableConic -

class
  ( Conic c
  , DualisableDiagrammatic r o d t n m
  , DualisableGBi r (->) o (ConeG c s p d t n m)
  , Transformable r s
  )
  => DualisableConic r o c s p d t n m

--------------------------------------------------------------------------------
-- NaturalConicSDualisable -

-- | natural transformation for 'Conic' objects from @'SDualBi' ('ConeG' __c s p d t n m__)@ to
-- @'SDualBi' ('Cone' __s p d t n m__)@.
class
  ( Conic c
  , NaturalDiagrammaticSDualisable h d t n m
  , NaturalTransformable h (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (Cone s p d t n m))
  )
  => NaturalConicSDualisable h c s p d t n m

instance
  ( NaturalConicBi h c s p d t n m
  , DualisableConic r o c s p d t n m
  )
  => ApplicativeG (SDualBi (ConeG c s p d t n m)) (HomDisj r o h) (->) where
  amapG (HomDisj h) = smapBi h

instance
  ( NaturalConicBi h c s p d t n m
  , DualisableConic r o c s p d t n m
  )
  => ApplicativeG (ConeG c s p d t n m) (Variant2 Covariant (HomDisj r o h)) (->) where
  amapG (Covariant2 h) c = c' where
    SDualBi (Right1 c') = amapG h (SDualBi (Right1 c))

instance
  ( NaturalConicBi h c Mlt p d t n m
  , DualisableConic r o c Mlt p d t n m
  , HomMultiplicative h
  , DualisableMultiplicative r o 
  , NaturalDiagrammaticDual1 h d t n m
  )
  => NaturalTransformable (Variant2 Covariant (HomDisj r o h)) (->)
       (ConeG c Mlt p d t n m) (Cone Mlt p d t n m)


instance
  ( NaturalConicBi h c Mlt p d t n m
  , DualisableConic r o c Mlt p d t n m
  , HomMultiplicative h
  , DualisableMultiplicative r o 
  , NaturalDiagrammaticDual1 h d t n m
  )
  => NaturalConic (Variant2 Covariant (HomDisj r o h)) c Mlt p d t n m

--------------------------------------------------------------------------------
-- prpNaturalConicConeOS -

-- | validity according to 'NaturalConic' for @'Cone' 'Mlt' __p__ 'Diagram' __t n m__@ on
-- @'HomDisj' 'Mlt' 'Op' ('HomId' 'Mlt')@,
prpNaturalConicConeOS :: Statement
prpNaturalConicConeOS = error "nyi"
