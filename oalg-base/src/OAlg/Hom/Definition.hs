
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
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
  , IsoOp, isoOp
  , HomDisjEmpty


    -- * Empty
  , HomEmpty

    -- * X
  , xscmHomDisj
  )
  where

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Variant

import OAlg.Structure.Oriented

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

instance ( Morphism h, ApplicativeG d h c, DualisableG s c o d
         , TransformableGObjectClassRange d s c
         )
  => ApplicativeG d (HomDisj s o h) c where
  amapG (HomDisj h) = amapG h

instance ( Morphism h, ApplicativeG d h c, DualisableG s c o d
         , TransformableGObjectClassRange d s c
         )
  => FunctorialG d (HomDisj s o h) c

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

instance ApplicativeG t (HomEmpty s) c where amapG = fromHomEmpty

instance Morphism (HomEmpty s) where
  type ObjectClass (HomEmpty s) = s
  domain = fromHomEmpty
  range  = fromHomEmpty

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
-- IsoOp -

type IsoOp s x = Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)

--------------------------------------------------------------------------------
-- isoOp -

-- | the canonical 'Contravariant' isomorphism between @__x__@ and @'Op' __x__@
isoOp :: TransformableGRefl Op s
  => Struct s x -> Variant2 Contravariant (Inv2 (HomDisjEmpty s Op)) x (Op x)
isoOp s = Contravariant2 (Inv2 t f) where
  Contravariant2 t = cToDual s
  Contravariant2 f = cFromDual s


--------------------------------------------------------------------------------
-- xscmHomDisj -

-- | random variable for some composable 'HomDisj'.
xscmHomDisj :: (TransformableG o s s, Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SHom s s o h)) -> X (SomeMorphism h) -> X (SomeCmpb2 (HomDisj s o h))
xscmHomDisj xo = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomDisj f) (HomDisj g)) . xSctSomeCmpb2 10 xo





  


