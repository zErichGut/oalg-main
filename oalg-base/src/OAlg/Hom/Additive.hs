
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
  (
    -- * Additive
    HomAdditive

    -- * Proposition
  , prpHomAdd1, prpHomAdd2

  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.Additive

import OAlg.Hom.Oriented
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
instance (TransformableFbr s, TransformableAdd s) => HomAdditive (IdHom s)

--------------------------------------------------------------------------------
-- DualisableAdditve -

class (DualisableFibredOriented s o, Transformable s Add) => DualisableAdditve s o

instance ( TransformableOrt s, TransformableAdd s, TransformableFbrOrt s
         , TransformableOp s
         ) => DualisableAdditve s Op

instance ( HomFibredOriented h, HomAdditive h, DualisableAdditve s o
         ) => HomAdditive (HomDisj s o h)


relDualisableAdditiveAdd2 :: DualisableAdditve s o
  => q o -> Struct s x -> Struct Add x -> Struct Add (o x) -> Adbl2 x -> Statement
relDualisableAdditiveAdd2 q s Struct Struct (Adbl2 a b)
  = (toDualArw q s (a + b) == toDualArw q s a + toDualArw q s b) :?> Params []  

relDualisableAdditveAdd1 :: DualisableAdditve s o
  => q o -> Struct s x -> Struct Add x -> Struct Add (o x) -> Root x -> Statement
relDualisableAdditveAdd1 q s Struct Struct rx
  = (toDualArw q s (zero rx) == zero (toDualRt q s rx)) :?> Params []

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


