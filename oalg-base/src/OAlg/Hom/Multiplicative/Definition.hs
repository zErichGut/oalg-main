

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}


-- |
-- Module      : OAlg.Hom.Multiplicative.Definition
-- Description : definition of homomorphisms between multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of homomorphisms between 'Multiplicative' structures.
module OAlg.Hom.Multiplicative.Definition
  (
    -- * Multiplicative
    HomMultiplicative, IsoMultiplicative

    -- * OpHom
  -- , toOpHomMlt
  , isoFromOpOpMlt
  , isoOppositeMlt
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Constructable

-- this modules are imported to make the description easier
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomMultiplicative -

-- | type family of homomorphisms between 'Multiplicative' structures.
--
--   __Propoerty__ Let __@h@__ be a type instance of the class 'HomMultiplicative', then
--   for all __@a@__, __@b@__ and @f@ in __@h@__ __@a@__ __@b@__ holds:
--
--   (1) #HomMlt1#For all @p@ in @'Point' __a__@ holds:
--       @'amap' f ('one' p) '==' 'one' ('pmap' f p)@.
--
--   (2) #HomMlt2#For all @x@, @y@ in __@a@__ with @'start' x '==' 'end' y@ holds:
--       @'amap' f (x '*' y) '==' 'amap' f x '*' 'amap' f y@.
--
--  Such a __@h@__ will be called a
--  __/family of homomorphisms between multiplicative structures/__ and an entity @f@ of
--  __@h@__ __@a@__ __@b@__ a __/multiplicative homomorphism/__ between __@a@__ and
-- __@b@__.
--
-- __Note__ If we interpret the types @__a__@ and @__b__@ as small categories (see note at
-- 'Multiplicative') then we can interpret the type family @__h__@ as a family of covariant
-- functors.
class (EmbeddableMorphism h Mlt, HomOriented h) => HomMultiplicative h

instance HomMultiplicative h => HomMultiplicative (Path h)

instance ( HomMultiplicative h, Transformable1 Op t
         , ForgetfulMlt t, ForgetfulTyp t, Typeable t
         )
  => HomMultiplicative (Forget t h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Mlt h = HomMultiplicative h

--------------------------------------------------------------------------------
-- IsoMultiplicative -

-- | isomorphisms between 'Multiplicative' structures.
type IsoMultiplicative h = ( FunctorialHomOriented h, Cayleyan2 h
                           , HomMultiplicative h
                           )

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance (TransformableOp s, ForgetfulMlt s, ForgetfulTyp s, Typeable s)
  => HomMultiplicative (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance (TransformableOp s, ForgetfulMlt s, ForgetfulTyp s, Typeable s)
  => HomMultiplicative (HomOp s)

instance (TransformableOp s, ForgetfulMlt s, ForgetfulTyp s, Typeable s)
  => HomMultiplicative (IsoOp s)

--------------------------------------------------------------------------------
-- isoFromOpOpMlt -

-- | the induced isomorphism of 'Multiplicative' structures given by 'FromOpOp'.
isoFromOpOpMlt :: Multiplicative a => IsoOp Mlt (Op (Op a)) a
isoFromOpOpMlt = make (FromOpOp :. IdPath Struct)

--------------------------------------------------------------------------------
-- isoOppositeMlt -

-- | the induced isomorphism of 'Oriented' structures given by 'Opposite'.
isoOppositeMlt :: Entity p => IsoOp Mlt (Op (Orientation p)) (Orientation p)
isoOppositeMlt = make (Opposite :. IdPath Struct)

--------------------------------------------------------------------------------
-- OpHom -

instance HomMultiplicative h => HomMultiplicative (OpHom h)
