
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Hom.Vectorial
-- Description : homomorphisms between vectorial structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Vectorial' structures having the same associated 'Scalar'.
module OAlg.Hom.Vectorial
  (
    -- * Vectorial
    HomVectorial
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Vectorial

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Additive

--------------------------------------------------------------------------------
-- HomVectorial -

-- | type family of homomorphisms between 'Vectorial' structures having the same associated 'Scalar.
--
-- __Property__ Let @__h__@ be a type instance of the class @'HomVectorial' __k__@, then
-- for all @__a__@, @__b__@, @v@ in @__h__ __a__ __b__@ and @x@ in @__k__@ holds:
-- @'amap' h (x '!' v) '==' x '!' 'amap' h v@.
class (HomAdditive h, Transformable (ObjectClass h) (Vec k)) => HomVectorial k h


instance HomVectorial k h => HomVectorial k (Path h)

instance ( TransformableFbr (s k), TransformableTyp (s k)
         , TransformableAdd (s k)
         , TransformableVec k s
         )
  => HomVectorial k (IdHom (s k))

--------------------------------------------------------------------------------
-- Hom -

type instance Hom (Vec k) h = HomVectorial k h


