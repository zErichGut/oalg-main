
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
-- Module      : OAlg.Hom.Oriented.Disjunctive
-- Description : definition of disjunctive homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of disjunctive homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Disjunctive
  (
    -- * Disjunctive
    HomOrientedDisjunctive, omapDisj

    -- * Applicative
  , FunctorialOriented

  , module V
  
    -- * HomDisj
  , HomDisj(..), homDisj
  , HomDisjEmpty

    -- * Dualisable
  , DualisableOriented
  , toDualArw, toDualPnt, toDualOrt
  
    -- * Iso
  , IsoOp, isoOp, isoOpOrt

    -- * X
  , xscmHomDisj
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Path
import OAlg.Category.Unify

import OAlg.Data.Variant as V

import OAlg.Structure.Oriented hiding (Path(..))

import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- omapDisj -

-- | induced application respecting the variant.
omapDisj :: (ApplicativePoint h, Disjunctive2 h)
  => h x y -> Orientation (Point x) -> Orientation (Point y)
omapDisj h = case variant2 h of
  Covariant     -> omap h
  Contravariant -> opposite . omap h

--------------------------------------------------------------------------------
-- HomOrientedDisjunctive -

-- | disjunctive homomorphism between 'Oriented' structures.
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
-- @'amap' h '.' 'orientation' '.=.' 'orientation' '.' 'omapDisj' h@. 
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      , Disjunctive2 h
      )
  => HomOrientedDisjunctive h

instance TransformableOrt s => HomOrientedDisjunctive (IdHom s)
instance HomOrientedDisjunctive h => HomOrientedDisjunctive (Path h)

--------------------------------------------------------------------------------
-- FunctorialOriented -

-- | functorial homomorphisms between 'Oriented' structures. 
class (CategoryDisjunctive h, HomOrientedDisjunctive h, Functorial h, FunctorialPoint h)
  => FunctorialOriented h

--------------------------------------------------------------------------------
-- DualisableOriented -

-- | duality according to @__o__@ on 'Oriented'-structures
--
-- __Properties__ Let @'DualisableOriented' __o s__@ then for all @__x__@
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

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
toDualArw :: DualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw _ s = fromIdG (toDualG' (d s) s) where
  d :: DualisableOriented s o => Struct s x -> DualityG s (->) o Id
  d _ = DualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
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
-- HomDisj -

newtype HomDisj s o h x y = HomDisj (SHom s s o h x y)
  deriving (Show,Show2,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomDisj s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomDisj s o h x y)

instance HomOriented h => Morphism (HomDisj s o h) where
  type ObjectClass (HomDisj s o h) = s
  homomorphous (HomDisj h) = homomorphous h

instance HomOriented h => Category (HomDisj s o h) where
  cOne = HomDisj . cOne 
  HomDisj f . HomDisj g = HomDisj (f . g)

instance HomOriented h => CategoryDisjunctive (HomDisj s o h)

instance (HomOriented h, TransformableGRefl o s) => CategoryDualisable o (HomDisj s o h) where
  cToDual s   = Contravariant2 (HomDisj t) where Contravariant2 t = cToDual s
  cFromDual s = Contravariant2 (HomDisj f) where Contravariant2 f = cFromDual s

instance (HomOriented h, DualisableOriented s o) => ApplicativeG Id (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Id (HomDisj s o h) (->)


instance (HomOriented h, DualisableOriented s o) => ApplicativeG Pnt (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Pnt (HomDisj s o h) (->)

instance (HomOriented h, DualisableOriented s o) => HomOrientedDisjunctive (HomDisj s o h)

--------------------------------------------------------------------------------
-- homDisj -

-- | embedding of 'HomOriented' to 'HomDisj'.
homDisj :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> Variant2 Covariant (HomDisj s o h) x y
homDisj h = Covariant2 (HomDisj h') where Covariant2 h' = sCov h

--------------------------------------------------------------------------------
-- HomDisjEmpty -

type HomDisjEmpty s o = HomDisj s o (HomEmpty s)

instance TransformableGObjectClassDomain Id (HomDisj OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableGObjectClassDomain Pnt (HomDisj OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableObjectClass OrtX (HomDisj OrtX Op (HomEmpty OrtX))
instance Transformable s Typ => EqExt (HomDisjEmpty s Op)

--------------------------------------------------------------------------------
-- IsoOp -

type IsoOp s x = Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)

--------------------------------------------------------------------------------
-- isoOp -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOp :: (TransformableOrt s, TransformableGRefl Op s)
  => Struct s x -> Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)
isoOp s = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual s
  Contravariant2 f = cFromDual s


--------------------------------------------------------------------------------
-- isoOpOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpOrt :: Oriented x => Variant2 Contravariant (Inv2 (HomDisjEmpty Ort Op)) x (Op x)
isoOpOrt = isoOp Struct

--------------------------------------------------------------------------------
-- xscmHomDisj -

-- | random variable for some composable 'HomDisj'.
xscmHomDisj :: (TransformableG o s s, Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SHom s s o h)) -> X (SomeMorphism h) -> X (SomeCmpb2 (HomDisj s o h))
xscmHomDisj xo = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomDisj f) (HomDisj g)) . xSctSomeCmpb2 10 xo

