
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Hom.Additive
-- Description : homomorphisms between additive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Additive' structures
module OAlg.Hom.Additive
  ( -- * Additive
    HomAdditive

    -- * Proposition
  , prpHomAdd1, prpHomAdd2
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Additive

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Fibred

--------------------------------------------------------------------------------
-- HomAdditive -

-- | type family of homomorphisms between 'Additive' structures.
--
-- __Property__ Let @__h__@ be a type instance of the class 'HomAdditive', then
-- for all @__a__@, @__b__@ and @f@ in @__h__@ @__a__@ @__b__@ holds:
--
-- (1) #HomAdd1#For all @r@ in @'Root' __a__@ holds:
-- @'amap' f ('zero' r) '==' 'zero' ('rmap' f r)@.
--
-- (2) #HomAdd2#For all @x@ and @y@ in @__a__@ with @'root' x '==' 'root' y@ holds:
-- @'amap' f (x '+' y) ) '==' 'amap' f x '+' 'amap' f y@.
--
--  Such a @__h__@ will be called a
--  __/family of homomorphisms between additive structures/__ and an entity @f@ of
--  @__h__@ @__a__@ @__b__@ a __/additive homomorphism/__ between @__a__@ and
-- @__b__@.
class (HomFibred h, Transformable (ObjectClass h) Add) => HomAdditive h

instance HomAdditive h => HomAdditive (Path h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Add h = HomAdditive h

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance (TransformableFbr s, TransformableTyp s, TransformableAdd s) => HomAdditive (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableFbr s
         , TransformableFbrOrt s, TransformableAdd s
         , Typeable s
         )
  => HomAdditive (HomOp s)

instance ( TransformableOrt s, TransformableTyp s, TransformableOp s
         , TransformableFbr s
         , TransformableFbrOrt s, TransformableAdd s
         , Typeable s
         )
  => HomAdditive (IsoOp s)

--------------------------------------------------------------------------------
-- OpHom -

instance (HomAdditive h, HomFibredOriented h) => HomAdditive (OpHom h)

--------------------------------------------------------------------------------
-- prpHomAdd1 -

relHomAdd1Homomorphous :: (HomAdditive h, Show2 h)
  => Homomorphous Add a b -> h a b -> Root a -> Statement
relHomAdd1Homomorphous (Struct :>: Struct) f r
  = (amap f (zero r) == zero (rmap f r)) :?> Params ["f":=show2 f,"r":=show r]

-- | validity according to "OAlg.Hom.Additive#HomAdd1".
prpHomAdd1 :: (HomAdditive h, Show2 h) => h a b -> Root a -> Statement
prpHomAdd1 f r = Prp "HomAdd1"
  :<=>: relHomAdd1Homomorphous (tauHom (homomorphous f)) f r

--------------------------------------------------------------------------------
-- prpHomAdd2 -

relHomAdd2Homomorphous :: (HomAdditive h, Show2 h)
  => Homomorphous Add a b -> h a b -> Adbl2 a -> Statement
relHomAdd2Homomorphous (Struct:>:Struct) f (Adbl2 x y)
  = (amap f (x+y) == amap f x + amap f y):?>Params ["f":=show2 f,"x":=show x,"y":=show y]

-- | validity according to "OAlg.Hom.Additive#HomAdd2".
prpHomAdd2 :: (HomAdditive h, Show2 h) => h a b -> Adbl2 a -> Statement
prpHomAdd2 f xy = Prp "HomAdd2"
  :<=>: relHomAdd2Homomorphous (tauHom (homomorphous f)) f xy

