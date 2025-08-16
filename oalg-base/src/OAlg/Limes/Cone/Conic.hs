
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
  , ApplicativeConicBi

    -- * Natural
  , NaturalConic, NaturalConicDual1
  , NaturalConicBi

  , NaturalConicSDualisable

    -- * Duality
  , DualisableConic, DualisableConicBi
  , DualisableConicDual1
    
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
import OAlg.Structure.Distributive

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

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

instance ApplicativeG (ConeG c s p d t n m) (HomEmpty r) (->) where
  amapG = fromHomEmpty

instance ApplicativeGDual1 (ConeG c s p d t n m) (HomEmpty r) (->)
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

-- | duality for 'Conic' objects.
--
-- __Property__ Let @'DualisableConic' __r o c s p d t n m__@ then
-- for all @__x__@ and @r@ in @'Struct' __r x__@ holds:
--
-- (1) For @__s__@ equal to t'Mlt', @'DualisableMultiplicative' __r o__@ and any proxy
-- @q@ in @__q r o c__ t'Mlt' __p d t n m__@ holds:
--
--     (1) @'cone' '.' 'toDualCncLft'' d r '.=.' 'toDualGLft' r '.' 'cone'@.
--
--     (2) @'cone' '.' 'toDualCncRgt'' d r '.=.' 'toDualGRgt' r '.' 'cone'@.
--
-- (2) For @__s__@ equal to t'Dst', @'DualisableDistributive' __r o__@ and any proxy
-- @q@ in @__q r o c__ t'Dst' __p d t n m__@ holds:
--
--     (1) @'cone' '.' 'toDualCncLft'' d r '.=.' 'toDualGLft' r '.' 'cone'@.
--
--     (2) @'cone' '.' 'toDualCncRgt'' d r '.=.' 'toDualGRgt' r '.' 'cone'@.
--
-- (see 'prpDualisableConicLft' and 'prpDualisableConicRgt')
class
  ( Conic c
  , DualisableGBi r (->) o (ConeG c s p d t n m)
  , DualisableDiagrammaticBi r o d t n m
  , p ~ Dual (Dual p), t ~ Dual (Dual t)
  )
  => DualisableConic r o c s p d t n m

--------------------------------------------------------------------------------
-- DualityConic -

-- | whiteness for 'DualisableConic'.
data DualityConic r o c s p d t n m where
  DualityConic :: DualisableConic r o c s p d t n m => DualityConic r o c s p d t n m
  
--------------------------------------------------------------------------------
-- toDualCncLft -

-- | the induced mapping.
toDualCncLft :: DualisableConic r o c s p d t n m
  => Struct r x -> c s p d t n m x -> c s (Dual p) d (Dual t) n m (o x)
toDualCncLft r c = c' where ConeG c' = toDualGLft r (ConeG c)

-- | the induced mapping.
toDualCncLft' :: DualisableConic r o c s p d t n m
  => q r o c s p d t n m -> Struct r x -> c s p d t n m x -> c s (Dual p) d (Dual t) n m (o x)
toDualCncLft' _ = toDualCncLft

--------------------------------------------------------------------------------
-- toDualCncRgt -

-- | the induced mapping.
toDualCncRgt :: DualisableConic r o c s p d t n m
  => Struct r x -> c s (Dual p) d (Dual t) n m x -> c s p d t n m (o x)
toDualCncRgt r c' = c where ConeG c = toDualGRgt r (ConeG c')

-- | the induced mapping.
toDualCncRgt' :: DualisableConic r o c s p d t n m
  => q r o c s p d t n m
  -> Struct r x -> c s (Dual p) d (Dual t) n m x -> c s p d t n m (o x)
toDualCncRgt' _ = toDualCncRgt

--------------------------------------------------------------------------------
-- prpDualisableConicLft -

relDualisableConicLftMlt ::
  ( s ~ Mlt
  , DualisableConic r o c s p d t n m
  , DualisableMultiplicative r o
  , TransformableMlt r -- acutally this follows from DualisableMultiplicative r o
  , Eq (d (Dual t) n m (o x))
  )
  => DualityConic r o c s p d t n m
  -> Struct r x -> c s p d t n m x -> Statement
relDualisableConicLftMlt d@DualityConic r c
  = ( cone (toDualCncLft' d r c) == toDualGLft r (cone c)
    ) :?> Params []

relDualisableConicLftDst ::
  ( s ~ Dst
  , DualisableConic r o c s p d t n m
  , DualisableDistributive r o
  , TransformableDst r
  , Eq (d (Dual t) n m (o x))
  )
  => DualityConic r o c s p d t n m
  -> Struct r x -> c s p d t n m x -> Statement
relDualisableConicLftDst d@DualityConic r c
  = ( cone (toDualCncLft' d r c) == toDualGLft r (cone c)
    ) :?> Params []

--------------------------------------------------------------------------------
-- prpDualisableConicRgt -

relDualisableConicRgtMlt ::
  ( s ~ Mlt
  , DualisableMultiplicative r o
  , TransformableMlt r
  , Eq (d t n m (o x))
  )
  => DualityConic r o c s p d t n m
  -> Struct r x -> c s (Dual p) d (Dual t) n m x -> Statement
relDualisableConicRgtMlt d@DualityConic r c
  = ( cone (toDualCncRgt' d r c) == toDualGRgt r (cone c) 
    ) :?> Params []

relDualisableConicRgtDst ::
  ( s ~ Dst
  , DualisableDistributive r o
  , TransformableDst r
  , Eq (d t n m (o x))
  )
  => DualityConic r o c s p d t n m
  -> Struct r x -> c s (Dual p) d (Dual t) n m x -> Statement
relDualisableConicRgtDst d@DualityConic r c
  = ( cone (toDualCncRgt' d r c) == toDualGRgt r (cone c) 
    ) :?> Params []

--------------------------------------------------------------------------------
-- DualisableConicDual1 -

-- | helper class to avoid undecidable instances.
class DualisableConic r o c s (Dual p) d (Dual t) n m => DualisableConicDual1 r o c s p d t n m

-- | constrains for conic objects @__c__@ which are bi-dualisable conic.
type DualisableConicBi r o c s p d t n m
  = ( DualisableConic r o c s p d t n m
    , DualisableConicDual1 r o c s p d t n m
    )


--------------------------------------------------------------------------------
-- crohS -

-- | natural assocition induced by 'croh' betewwn @'SDualBi' ('ConeG' __c s p d t n m__)@ and
-- @'SDualBi' ('Cone' __s p d t n m__)@.
crohS :: Conic c => SDualBi (ConeG c s p d t n m) x -> SDualBi (Cone s p d t n m) x
crohS (SDualBi (Right1 c)) = SDualBi (Right1 (croh c))
crohS (SDualBi (Left1 c')) = SDualBi (Left1 (croh c'))

instance Conic c
  => Natural r (->) (SDualBi (ConeG c s p d t n m)) (SDualBi (Cone s p d t n m)) where
  roh _ = crohS

--------------------------------------------------------------------------------
-- ApplicativeConicBi -

-- | helper class to avoid undecidable instances.
class ApplicativeGBi (ConeG c s p d t n m) h (->) => ApplicativeConicBi h c s p d t n m

instance ApplicativeConicBi (HomEmpty r) c Mlt p d t n m

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
  ( Morphism h
  , ApplicativeGBi (ConeG c s p d t n m) h (->)
  , DualisableGBi r (->) o (ConeG c s p d t n m)
  )
  => ApplicativeG (SDualBi (ConeG c s p d t n m)) (HomDisj r o h) (->) where
  amapG (HomDisj h) = amapG h -- i.e. smapBi

instance
  ( Morphism h
  , ApplicativeGBi (ConeG c s p d t n m) h (->)
  , DualisableGBi r (->) o (ConeG c s p d t n m)
  )
  => ApplicativeG (ConeG c s p d t n m) (Variant2 Covariant (HomDisj r o h)) (->) where
  amapG (Covariant2 h) c = c' where
    SDualBi (Right1 c') = amapG h (SDualBi (Right1 c))

instance
  ( HomMultiplicative h
  , TransformableMlt r
  , NaturalDiagrammaticBi h d t n m
  , ApplicativeGBi (ConeG c Mlt p d t n m) h (->)
  
  , DualisableMultiplicative r o
  , DualisableConic r o c Mlt p d t n m  
  )
  => NaturalTransformable (HomDisj r o h) (->)
       (SDualBi (ConeG c Mlt p d t n m)) (SDualBi (Cone Mlt p d t n m))

instance
  ( ApplicativeConicBi h c Mlt p d t n m
  , HomMultiplicative h
  , NaturalDiagrammaticBi h d t n m
  , DualisableMultiplicative r o
  , TransformableMlt r
  
  , DualisableConic r o c Mlt p d t n m  
  )
  => NaturalConicSDualisable (HomDisj r o h) c Mlt p d t n m

instance
  ( ApplicativeGBi (ConeG c Mlt p d t n m) h (->)

  , HomMultiplicative h
  , NaturalDiagrammaticBi h d t n m
  , DualisableMultiplicative r o

  , DualisableConic r o c Mlt p d t n m
  )
  => NaturalTransformable (Variant2 Covariant (HomDisj r o h)) (->)
       (ConeG c Mlt p d t n m) (Cone Mlt p d t n m)


instance
  ( ApplicativeGBi (ConeG c Mlt p d t n m) h (->)

  , HomMultiplicative h
  , NaturalDiagrammaticBi h d t n m
  , DualisableMultiplicative r o

  , DualisableConic r o c Mlt p d t n m
  )
  => NaturalConic (Variant2 Covariant (HomDisj r o h)) c Mlt p d t n m


--------------------------------------------------------------------------------
-- prpNaturalConicConeOS -

-- | validity according to 'NaturalConic' for @'Cone' 'Mlt' __p__ 'Diagram' __t n m__@ on
-- @'HomDisj' 'Mlt' 'Op' ('HomId' 'Mlt')@,
prpNaturalConicConeOS :: Statement
prpNaturalConicConeOS = error "nyi"
