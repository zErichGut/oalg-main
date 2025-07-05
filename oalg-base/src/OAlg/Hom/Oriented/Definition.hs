
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
  , DualisableOriented
  , toDualArw, toDualPnt
  
    -- * Applicative
  , FunctorialOriented

    -- * Instances
    -- ** HomOrt    
  , HomOrt(..), homOrt

    -- ** HomOrtEmpty
  , HomOrtEmpty, isoOpOrt

  , module V
  )
  where

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.SDuality

import OAlg.Data.Variant as V

import OAlg.Structure.Oriented.Definition hiding (Path(..))
import OAlg.Structure.Fibred.Definition

import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- FunctorialOriented -

-- | helper class to avoid undecidable instances.
class (CategoryDisjunctive h, HomDisjunctiveOriented h, Functorial h, FunctorialPoint h)
  => FunctorialOriented h 

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

instance (HomOriented h, DualisableOriented s o) => ApplicativeG Id (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Id (HomOrt s o h) (->)


instance (HomOriented h, DualisableOriented s o) => ApplicativeG Pnt (HomOrt s o h) (->) where
  amapG (HomOrt h) = amapG h

instance (HomOriented h, DualisableOriented s o) => FunctorialG Pnt (HomOrt s o h) (->)

instance (HomOriented h, DualisableOriented s o) => HomDisjunctiveOriented (HomOrt s o h)

instance (HomOriented h, DualisableOriented s o) => FunctorialOriented (HomOrt s o h)


omapDisj :: (ApplicativePoint h, Disjunctive2 h)
  => h x y -> Orientation (Point x) -> Orientation (Point y)
omapDisj h = case variant2 h of
  Covariant     -> omap h
  Contravariant -> opposite . omap h

rmapDisjFbrtOrtStruct :: (ApplicativePoint h, Disjunctive2 h)
  => Homomorphous FbrOrt x y -> h x y -> Root x -> Root y
rmapDisjFbrtOrtStruct (Struct :>: Struct) = omapDisj

rmapDisjFbrOrt :: ( Morphism h, Transformable (ObjectClass h) FbrOrt
                  , ApplicativePoint h, Disjunctive2 h
                  )
  => h x y -> Root x -> Root y
rmapDisjFbrOrt h = rmapDisjFbrtOrtStruct (tauHom $ homomorphous h) h
  
instance ( HomOriented h, DualisableOriented s o
         , Transformable s FbrOrt
         ) => ApplicativeG Rt (HomOrt s o h) (->) where
  amapG = amapRt . rmapDisjFbrOrt
  
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
instance Transformable s Typ => EqExt (HomOrtEmpty s Op)

--------------------------------------------------------------------------------
-- isoOpOrt -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOpOrt :: Oriented x => Variant2 Contravariant (Inv2 (HomOrtEmpty Ort Op)) x (Op x)
isoOpOrt = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual Struct
  Contravariant2 f = cFromDual Struct
