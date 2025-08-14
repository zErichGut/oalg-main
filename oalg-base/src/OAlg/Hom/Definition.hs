
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Hom.Definition
-- Description : basic definitions of homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- basic definitions of homomorphisms.
module OAlg.Hom.Definition
  (
    -- * Disjunctive
    HomDisj(..), homDisj
  , HomDisjEmpty

    -- * Contravariant Isomorphism
  , IsoHomDisj, isoHomDisj
  , IsoO, isoO


    -- * Empty
  , HomEmpty, fromHomEmpty

    -- * Id
  , HomId(..)

    -- * Hom
  , Hom, HomD
    
    -- * X
  , xscmHomDisj
  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred

--------------------------------------------------------------------------------
-- HomDisj -

-- | disjunctive family of homomorphsims.
newtype HomDisj s o h x y = HomDisj (SHom s s o h x y)
  deriving (Show,Show2,Validable,Validable2,Disjunctive,Disjunctive2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (HomDisj s o h)
deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq (HomDisj s o h x y)

instance Morphism h => Morphism (HomDisj s o h) where
  type ObjectClass (HomDisj s o h) = s
  homomorphous (HomDisj h) = homomorphous h

instance Morphism h => Category (HomDisj s o h) where
  cOne = HomDisj . cOne 
  HomDisj f . HomDisj g = HomDisj (f . g)

instance Morphism h => CategoryDisjunctive (HomDisj s o h)


instance (Morphism h, TransformableGRefl o s) => CategoryDualisable o (HomDisj s o h) where
  cToDual s   = Contravariant2 (HomDisj t) where Contravariant2 t = cToDual s
  cFromDual s = Contravariant2 (HomDisj f) where Contravariant2 f = cFromDual s

instance (Morphism h, ApplicativeG Id h c, DualisableG s c o Id, c ~ (->))
  => ApplicativeG Id (HomDisj s o h) c where
  amapG (HomDisj h) = smap h

instance ( Morphism h, ApplicativeG Id h c, DualisableG s c o Id, c ~ (->))
  => FunctorialG Id (HomDisj s o h) c
  
--------------------------------------------------------------------------------
-- HomEmpty -

-- | the empty family of homomorphisms.
newtype HomEmpty s x y = HomEmpty (EntEmpty2 x y)
  deriving (Show, Show2,Eq,Eq2,EqExt,Validable,Validable2)

--------------------------------------------------------------------------------
-- fromHomEmpty -

-- | the empty map.
fromHomEmpty :: HomEmpty s a b -> x
fromHomEmpty (HomEmpty e) = fromEmpty2 e

--------------------------------------------------------------------------------
-- HomEmpty - Instances -

instance Morphism (HomEmpty s) where
  type ObjectClass (HomEmpty s) = s
  domain = fromHomEmpty
  range  = fromHomEmpty

instance ApplicativeG Id (HomEmpty s) c where amapG = fromHomEmpty
instance ApplicativeG Pnt (HomEmpty s) c where amapG = fromHomEmpty
instance ApplicativeG Rt (HomEmpty s) c where amapG = fromHomEmpty

--------------------------------------------------------------------------------
-- homDisj -

-- | embedding of 'HomOriented' to 'HomDisj'.
homDisj :: (Morphism h, Transformable (ObjectClass h) s)
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
-- IsoHomDisj -

-- | type for contravariant isomorphism of @'HomDisj' __s o h x (__o x__)@.
type IsoHomDisj s o h x = Variant2 Contravariant (Inv2 (HomDisj s o h)) x (o x)

--------------------------------------------------------------------------------
-- isoHomDisj -

-- | contravariant isomorphism for @'HomDisj' __s o h x (__o x__)@.
isoHomDisj :: (Morphism h, TransformableGRefl o s)
  => Struct s x -> IsoHomDisj s o h x
isoHomDisj s = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual s
  Contravariant2 f = cFromDual s

--------------------------------------------------------------------------------
-- IsoO -

type IsoO s o x = Variant2 Contravariant (Inv2 (HomDisjEmpty s o)) x (o x)

--------------------------------------------------------------------------------
-- isoO -

isoO :: TransformableGRefl o s
  => Struct s x -> IsoO s o x
isoO = isoHomDisj

--------------------------------------------------------------------------------
-- HomId -

-- | isomorphisms for mappings between @__x__@ and @'Id' __x__@ and vice versa.
data HomId s x y where
  ToId   :: (Structure s x, Structure s (Id x)) => HomId s x (Id x)
  FromId :: (Structure s x, Structure s (Id x)) => HomId s (Id x) x

deriving instance Show (HomId s x y)
instance Show2 (HomId s)

instance Morphism (HomId s) where
  type ObjectClass (HomId s) = s
  homomorphous ToId = Struct :>: Struct
  homomorphous FromId = Struct :>: Struct

instance ApplicativeG Id (HomId s) (->) where
  amapG ToId x = Id x
  amapG FromId (Id x) = x

instance ApplicativeG Pnt (HomId s) (->) where
  amapG ToId (Pnt p)   = Pnt p
  amapG FromId (Pnt p) = Pnt p
  
--------------------------------------------------------------------------------
-- Hom -

-- | homomorphisms parameterized over @__s__@.
type family Hom s (h :: Type -> Type -> Type) :: Constraint

--------------------------------------------------------------------------------
-- HomD -

-- | disjunctive homomorphisms parameterized over @__s__@.
type family HomD s (h :: Type -> Type -> Type) :: Constraint

--------------------------------------------------------------------------------
-- xscmHomDisj -

-- | random variable for some composable 'HomDisj'.
xscmHomDisj :: (TransformableG o s s, Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SHom s s o h)) -> X (SomeMorphism h) -> X (SomeCmpb2 (HomDisj s o h))
xscmHomDisj xo = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomDisj f) (HomDisj g)) . xSctSomeCmpb2 10 xo





  


