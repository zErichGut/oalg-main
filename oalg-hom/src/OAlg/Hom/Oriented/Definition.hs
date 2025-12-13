
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

    -- * Covariant
    HomOriented, homDisjOpOrt

    -- * Disjunctive
  , HomOrientedDisjunctive, omapDisj

    -- * Applicative
  , FunctorialOriented

  , module V
  
    -- * Duality
  , DualisableOriented
  , toDualArw, toDualPnt, toDualOrt
  
    -- * Iso
  , toDualOpOrt

  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.Path

import OAlg.Data.Variant as V

import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- HomOriented -

-- | covariant family of homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @__h__@ be an instance of 'HomOriented', then
-- for all  @__a__@, @__b__@ and @h@ in @__h a b__@ holds:
--
-- (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
-- (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
-- __Note__ The above property is equivalent to
-- @'amap' h '.' 'orientation' '.=.' 'orientation' '.' 'omap' h@. 
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      ) => HomOriented h where

instance HomOriented h => HomOriented (Path h)

instance TransformableOrt s => HomOriented (HomEmpty s)

instance HomOriented h => HomOriented (Id2 h)

instance TransformableOrt s => HomOriented (HomId s)

instance HomOriented h => HomOriented (Inv2 h)

--------------------------------------------------------------------------------
-- omapDisj -

-- | induced application respecting the variant by applying 'opposite' for 'Contravariant' cases. 
omapDisj :: (ApplicativePoint h, Disjunctive2 h)
  => h x y -> Orientation (Point x) -> Orientation (Point y)
omapDisj h = case variant2 h of
  Covariant     -> omap h
  Contravariant -> opposite . omap h

--------------------------------------------------------------------------------
-- HomOrientedDisjunctive -

-- | disjunctive family of homomorphism between 'Oriented' structures.
--
-- __Properties__ Let @'HomOrientedDisjunctive' __h__@, then
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
--
-- __Note__ The above property is equivalent to
-- @'orientation' '.' 'amap' h '.=.' 'omapDisj' h '.' 'orientation'@. 
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      , Disjunctive2 h
      )
  => HomOrientedDisjunctive h

instance HomOrientedDisjunctive h => HomOrientedDisjunctive (Path h)

instance
  ( CategoryDisjunctive h
  , HomOrientedDisjunctive h
  )
  => HomOrientedDisjunctive (Inv2 h)

instance HomOrientedDisjunctive h => HomOriented (Variant2 Covariant h)

instance
  ( Transformable s Ort
  , HomOrientedDisjunctive h
  )
  => HomOrientedDisjunctive (Sub s h)

--------------------------------------------------------------------------------
-- DualisableOriented -

-- | duality according to @__o__@ on 'Oriented' structures.
--
-- __Properties__ Let @'DualisableOriented' __o s__@, then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q s '.=.' 'toDualPnt' q s '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
--
-- __Note__ The above property is equivalent to
-- @'orientation' '.' 'toDualArw' q s '.=.' 'toDualOrt' q s '.' 'orientation'@.
class (DualisableG s (->) o Id, DualisableG s (->) o Pnt, Transformable s Ort)
  => DualisableOriented s o

instance (TransformableType s, TransformableOrt s, TransformableOp s) => DualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow given by @'DualisableOriented' __s o__@ and induced by
-- @'DualisableG __s__ (->) __o__ 'Id'@.
toDualArw :: DualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw _ s = fromIdG (toDualG' (d s) s) where
  d :: DualisableOriented s o => Struct s x -> DualityG s (->) o Id
  d _ = DualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point given by @'DualisableOriented' __s o__@ and induced by
-- @'DualisableG' __s__ (->) __o__ 'Pnt'@.
toDualPnt :: DualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) s) where
  d :: DualisableOriented s o => q o -> Struct s x -> DualityG s (->) o Pnt
  d _ _ = DualityG

--------------------------------------------------------------------------------
-- toDualOrt -

-- | the induced dual orientation.
toDualOrt :: DualisableOriented s o => q o -> Struct s x
  -> Orientation (Point x) -> Orientation (Point (o x))
toDualOrt q st (s :> e) = opposite (t s :> t e) where t = toDualPnt q st

--------------------------------------------------------------------------------
-- HomDisj - HomOrientedDisjunctive -

instance (HomOriented h, DualisableOriented s o) => HomOrientedDisjunctive (HomDisj s o h)

--------------------------------------------------------------------------------
-- FunctorialOriented -

-- | functorial morphismsm, i.e. 'Functorial' and 'FunctorialPoint'.
--
-- __Note__ It's not mandatory being an homomorphism!
class (Functorial h, FunctorialPoint h) => FunctorialOriented h

instance FunctorialOriented h => FunctorialOriented (Inv2 h)

instance (HomOriented h, DualisableOriented s o) => FunctorialOriented (HomDisj s o h)

--------------------------------------------------------------------------------
-- homDisjOpOrt -

-- | homomorphism on 'Oriented' structures as a 'Covariant' homomorphism in @'HomDisj' 'Ort' 'Op'@.
homDisjOpOrt :: HomOriented h => h x y -> Variant2 Covariant (HomDisj Ort Op h) x y
homDisjOpOrt = homDisj

--------------------------------------------------------------------------------
-- toDualOpOrt -

-- | the canonical 'Contravariant' isomorphism on 'Oriented' structures
-- between @__x__@ and @'Op' __x__@.
toDualOpOrt :: Oriented x => Variant2 Contravariant (IsoO Ort Op) x (Op x)
toDualOpOrt = toDualO Struct

