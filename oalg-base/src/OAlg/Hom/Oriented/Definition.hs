
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

    -- * Covariant
  , HomOriented, HomEmpty

    -- * Dualisable
  , SDualisableOriented
  , toDualArw, toDualPnt
  
    -- * Applicative
  , ApplicativePoint, pmap, omap
  , FunctorialPoint
  , FunctorialOriented

    -- * Instances
    -- ** HomOrt
    
  , HomOrt(..), homOrt

    -- ** HomOrtEmpty
  , HomOrtEmpty
  , toOpOrt, fromOpOrt

  , module V

  )
  where

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.SDuality

import OAlg.Data.Identity
import OAlg.Data.Variant as V

import OAlg.Structure.Oriented hiding (Path(..))

--------------------------------------------------------------------------------
-- ApplicativePoint -

-- | applications on 'Point's.
type ApplicativePoint h = ApplicativeG Pnt h (->)

--------------------------------------------------------------------------------
-- pmap -

-- | the induced mapping of 'Point's given by 'amapG'. 
pmap :: ApplicativePoint h => h x y -> Point x -> Point y
pmap h = fromPntG (amapG h)

--------------------------------------------------------------------------------
-- omap -

-- | the induced mapping of 'Orientation'.
omap :: ApplicativePoint h => h a b -> Orientation (Point a) -> Orientation (Point b)
omap = amapG . pmap

--------------------------------------------------------------------------------
-- FunctorialPoint -

type FunctorialPoint h = FunctorialG Pnt h (->)

--------------------------------------------------------------------------------
-- FunctorialOriented -

type FunctorialOriented h = (Functorial h, FunctorialPoint h)

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
  => HomDisjunctiveOriented h where

instance HomDisjunctiveOriented h => HomOriented (Variant2 Covariant h)
instance HomDisjunctiveOriented h => HomDisjunctiveOriented (Variant2 Contravariant h)

--------------------------------------------------------------------------------
-- SDualisableOriented -

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'SDualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q '.=.' 'toDualPnt' q '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q '==' 'toDualPnt' q '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG Ort (->) o Id, DualisableG Ort (->) o Pnt
      , Transformable s Ort, TransformableG o s s
      )
  => SDualisableOriented s o

instance (TransformableOrt s, TransformableOp s) => SDualisableOriented s Op

--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG __s__ (->) __o__ 'Id'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualArw :: SDualisableOriented s o => q o -> Struct s x -> x -> o x
toDualArw q s = fromIdG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Id
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' __s__ (->) __o__ 'Pnt'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualPnt :: SDualisableOriented s o => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) (tauOrt s)) where
  d :: SDualisableOriented s o => q o -> Struct s x -> SDualityG Ort (->) o Pnt
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- HomEmpty -

-- | the empty homomorphism.
newtype HomEmpty s x y = HomEmpty (EntEmpty2 x y)
  deriving (Show, Show2,Eq,Eq2,EqExt,Validable,Validable2)

--------------------------------------------------------------------------------
-- fromHomEmpty -

fromHomEmpty :: HomEmpty s a b -> x
fromHomEmpty (HomEmpty e) = fromEmpty2 e

--------------------------------------------------------------------------------
-- HomEmpty - Instances -

instance ApplicativeG t (HomEmpty s) c where amapG = fromHomEmpty

--------------------------------------------------------------------------------
-- HomEmpty - HomOriented -

instance Morphism (HomEmpty s) where
  type ObjectClass (HomEmpty s) = s
  domain = fromHomEmpty
  range  = fromHomEmpty

instance TransformableOrt s => HomOriented (HomEmpty s)

--------------------------------------------------------------------------------
-- HomOrt -

newtype HomOrt s o h x y = HomOrt (SHom Ort s o h x y)
  deriving (Show,Show2,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomOrt s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomOrt s o h x y)

instance HomOriented h => Morphism (HomOrt s o h) where
  type ObjectClass (HomOrt s o h) = s
  homomorphous (HomOrt h) = homomorphous h

instance HomOriented h => Category (HomOrt s o h) where
  cOne = HomOrt . cOne 
  HomOrt f . HomOrt g = HomOrt (f . g)

instance HomOriented h => CategoryDisjunctive (HomOrt s o h)

instance (HomOriented h, TransformableGRefl o s) => CategoryDualisable o (HomOrt s o h) where
  cToDual s   = Contravariant2 (HomOrt t) where Contravariant2 t = cToDual s
  cFromDual s = Contravariant2 (HomOrt f) where Contravariant2 f = cFromDual s

instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Id (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Id (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Id (HomOrt s o h) (->)


instance (HomOriented h, SDualisableOriented s o) => ApplicativeG Pnt (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, SDualisableOriented s o) => ApplicativeGMorphism Pnt (HomOrt s o h) (->)
instance (HomOriented h, SDualisableOriented s o) => FunctorialG Pnt (HomOrt s o h) (->)

instance (HomOriented h, SDualisableOriented s o) => HomDisjunctiveOriented (HomOrt s o h)

--------------------------------------------------------------------------------
-- homOrt -

-- | embedding of 'HomOriented' to 'HomOrt'.
homOrt :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> Variant2 Covariant (HomOrt s o h) x y
homOrt h = Covariant2 (HomOrt h') where Covariant2 h' = sCov h

--------------------------------------------------------------------------------
-- HomOrtEmpty -

type HomOrtEmpty s o = HomOrt s o (HomEmpty s)

instance TransformableGObjectClassDomain Id (HomOrt OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableGObjectClassDomain Pnt (HomOrt OrtX Op (HomEmpty OrtX)) EqEOrt
instance TransformableObjectClass OrtX (HomOrt OrtX Op (HomEmpty OrtX))
instance EqExt (HomOrtEmpty OrtX Op)

--------------------------------------------------------------------------------
-- toOpOrt -

toOpOrt :: Oriented x => Variant2 Contravariant (HomOrtEmpty Ort Op) x (Op x)
toOpOrt = cToDual Struct

--------------------------------------------------------------------------------
-- fromOpOrt -

fromOpOrt :: Oriented x => Variant2 Contravariant (HomOrtEmpty Ort Op) (Op x) x
fromOpOrt = cFromDual Struct

