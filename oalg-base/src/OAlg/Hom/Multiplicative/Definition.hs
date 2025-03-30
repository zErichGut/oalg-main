

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
  ( -- * Multiplicative
    HomMultiplicative, IsoMultiplicative

    -- * Duality
  , SDualityMultiplicative

    -- * OpHom
  -- , toOpHomMlt
  , isoToOpOpMlt, isoFromOpOpMlt
  -- , isoOppositeMlt
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

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
class (HomOriented h, Transformable (ObjectClass h) Mlt) => HomMultiplicative h

instance HomMultiplicative h => HomMultiplicative (Path h)

instance ( HomMultiplicative h, TransformableOp t
         , TransformableMlt t, TransformableTyp t
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

instance (TransformableOp s, TransformableOrt s, TransformableMlt s, TransformableTyp s)
  => HomMultiplicative (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance (TransformableOp s, TransformableOrt s, TransformableMlt s, TransformableTyp s)
  => HomMultiplicative (HomOp s)

instance (TransformableOp s, TransformableOrt s, TransformableMlt s, TransformableTyp s)
  => HomMultiplicative (IsoOp s)

--------------------------------------------------------------------------------
-- isoToOpOpMlt -

-- | the induced isomorphism of 'Multiplicative' structures given by 'ToOpOp'.
isoToOpOpMlt :: Multiplicative a => IsoOp Mlt a (Op (Op a))
isoToOpOpMlt = isoToOpOp

--------------------------------------------------------------------------------
-- isoFromOpOpMlt -

-- | the induced isomorphism of 'Multiplicative' structures given by 'FromOpOp'.
isoFromOpOpMlt :: Multiplicative a => IsoOp Mlt (Op (Op a)) a
isoFromOpOpMlt = isoFromOpOp

{-
--------------------------------------------------------------------------------
-- isoOppositeMlt -

-- | the induced isomorphism of 'Oriented' structures given by 'Opposite'.
isoOppositeMlt :: Entity p => IsoOp Mlt (Op (Orientation p)) (Orientation p)
isoOppositeMlt = make (Opposite :. IdPath Struct)
-}

--------------------------------------------------------------------------------
-- OpHom -

instance HomMultiplicative h => HomMultiplicative (OpHom h)

--------------------------------------------------------------------------------
-- Forget' -

instance ( HomMultiplicative h
         , Transformable t Ort
         , Transformable t Mlt
         , Transformable t Typ
         , Transformable1 Op t
         ) => HomMultiplicative (Forget' t h)

--------------------------------------------------------------------------------
-- SDualityMultiplicative -

-- | structural duality of a 'SDualityOriented' respecting the multiplicative structure.
--
-- __Properties__ For all @d@ in @__d__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDuality' __d__ __s__ __i__ __o__@ holds:
--
-- (1) @'sdlToDual' d s ('one' p) '==' 'one' ('sdlToDualPnt' d s p)@ for all @p@ in @'Point' __x__@.
--
-- (2) @'sdlToDual' d s (f '*' g) '==' 'sdlToDual' d s g '*' 'sdlToDual' d s f@ for all
-- @'Mltp2' f g@ in @'Mltp2' __x__@.
--
-- (3) @'sdlFromDual' d s ('one' p') '==' 'one' ('sdlFromDualPnt' d s p')@ for all
-- @p'@ in @'Point' (__o__ __x__)@.
--
-- (4) @'sdlFromDual' d s (f' '*' g') '==' 'sdlFromDual' d s g' '*' 'sdlFromDual' d s f'@ for all
-- @'Mltp2' f' g'@ in @'Mltp2' (__o__ __x__)@.
--
-- __Note__
--
-- (1) @'sdlToDual' d s@ together with @'sdlToDualPnt' d s@ and
-- @'sdlFromDual' d s@ together with @'sdlFromDualPnt' d s@ constitute a __contravariant__
-- homomorphisms between 'Multiplicative' structures.
class (SDualityOriented d s i o, HomMultiplicative i, Transformable s Mlt)
  => SDualityMultiplicative d s i o 

--------------------------------------------------------------------------------
-- OpDuality - SDualityMultiplicative -

instance ( TransformableTyp s, Transformable1 Op s, TransformableOp s, TransformableOrt s
         , TransformableMlt s
         )
  => SDualityMultiplicative OpDuality s (IsoOp s) Op
