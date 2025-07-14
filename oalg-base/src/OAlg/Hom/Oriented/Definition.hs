
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
-- Description : definition of covariant homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of covariant homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Definition
  (
    -- * Covariant
    HomOriented

    -- * Instances
  , IdHom(..), HomEmpty    
  )
  where

import OAlg.Prelude

import OAlg.Data.Variant

import OAlg.Category.Path

import OAlg.Structure.Oriented.Definition

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
--
-- __Note__ The above property is equivalent to
-- @'amap' h '.' 'orientation' '.=.' 'orientation' '.' 'omap' h@. 
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      ) => HomOriented h where

instance HomOriented h => HomOriented (Path h)
instance TransformableOrt s => HomOriented (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Disjunctive -

instance Disjunctive (IdHom s x y) where variant IdHom = Covariant
instance Disjunctive2 (IdHom s)

--------------------------------------------------------------------------------
-- IdHom -

data IdHom s x y where
  IdHom :: Structure s x => IdHom s x x

deriving instance Show (IdHom s x y)
instance Show2 (IdHom s)

deriving instance Eq (IdHom s x y)
instance Eq2 (IdHom s)

instance Validable (IdHom s x y) where valid IdHom = SValid
instance Validable2 (IdHom s)

--------------------------------------------------------------------------------
-- IdHom - Category -

instance Morphism (IdHom s) where
  type ObjectClass (IdHom s) = s
  homomorphous IdHom = Struct :>: Struct

instance Category (IdHom s) where
  cOne Struct = IdHom
  IdHom . IdHom = IdHom

instance Cayleyan2 (IdHom s) where
  invert2 IdHom = IdHom

--------------------------------------------------------------------------------
-- IdHom - Applicative -

-- instance ApplicativeG f (IdHom s) (->) where amapG IdHom = id
instance (Category b, TransformableGObjectClassRange f s b)
  => ApplicativeG f (IdHom s) b where amapG i@IdHom = cOne (tauG (domain i))

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


