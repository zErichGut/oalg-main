
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

    -- * Duality
  , DualisableAdditive
  
    -- * Proposition
  , prpHomAdd1, prpHomAdd2
  , prpDualisableAdditiveAdd1, prpDualisableAdditiveAdd2
  , prpHomDisjOpAdd
  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

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
instance (TransformableFbr s, TransformableAdd s) => HomAdditive (HomEmpty s)

--------------------------------------------------------------------------------
-- DualisableAdditive -

-- | duality according to @__o__@ on 'Additive'-structures
--
-- __Properties__ Let @'DualisableAdditive' __s o___@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
--
-- (1) For all @r@ in @'Root' __x__@ holds:
-- @'toDualArw' q s ('zero' r) '==' 'zero' ('toDualRt' q s r)@,
--
-- (2) For all @a@, @b@ in @__x__@ with @'root' a '==' 'root' b@ holds:
-- @'toDualArw' q s (a '+' b) '==' 'toDualArw' q s a '+' 'toDualArw' q s b@.
--
-- where @q@ is any proxy for @__o__@.
class (DualisableFibredOriented s o, Transformable s Add) => DualisableAdditive s o

instance ( TransformableOrt s, TransformableAdd s, TransformableFbrOrt s
         , TransformableOp s, TransformableType s
         ) => DualisableAdditive s Op

instance ( HomFibredOriented h, HomAdditive h, DualisableAdditive s o
         ) => HomAdditive (HomDisj s o h)

--------------------------------------------------------------------------------
-- prpDualisableAdditiveAdd1 -
relDualisableAdditiveAdd1 :: DualisableAdditive s o
  => q o -> Struct s x -> Struct Add x -> Struct Add (o x) -> Root x -> Statement
relDualisableAdditiveAdd1 q s Struct Struct r
  = (toDualArw q s (zero r) == zero (toDualRt q s r)) :?> Params ["r":=show r]

-- | validity according to 'DualisableAdditive', property 1.
prpDualisableAdditiveAdd1 :: DualisableAdditive s o
  => q o -> Struct s x -> Root x -> Statement
prpDualisableAdditiveAdd1 q s r = Prp "DualisableAdditiveAdd1"
  :<=>: relDualisableAdditiveAdd1 q s (tau s) (tau (tauO s)) r

--------------------------------------------------------------------------------
-- prpDualisableAdditiveAdd2 -
relDualisableAdditiveAdd2 :: DualisableAdditive s o
  => q o -> Struct s x -> Struct Add x -> Struct Add (o x) -> Adbl2 x -> Statement
relDualisableAdditiveAdd2 q s Struct Struct ad@(Adbl2 a b)
  = (toDualArw q s (a + b) == toDualArw q s a + toDualArw q s b) :?> Params ["ad":=show ad]  
-- root (toDualArrw q s x) == orientation (toDualArw q s x)       :: Transformable s FbrOrt
-- orientation (toDualArw q s x) == toDualOrt q s (orientation x) :: DualisableOriented s o
-- toDualOrt q s (orientation x) == toDualOrt q s (root x)        :: Transformable s FbrOrt
-- toDualOrt q s (root x) == toDualRt (root x)                    :: DualisableFibredOriented s o
--
-- this shows that the above equation is valid!

-- | validity according to 'DualisableAdditive', property 2.
prpDualisableAdditiveAdd2 :: DualisableAdditive s o
  => q o -> Struct s x -> Adbl2 x -> Statement
prpDualisableAdditiveAdd2 q s ad = Prp "DualisableAdditiveAdd2"
  :<=>: relDualisableAdditiveAdd2 q s (tau s) (tau (tauO s)) ad

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

--------------------------------------------------------------------------------
-- AddX -

data AddX

type instance Structure AddX x = (Additive x, FibredOriented x, XStandardAdd x)

instance Transformable AddX Ort where tau Struct = Struct
instance TransformableOrt AddX

instance Transformable AddX Fbr where tau Struct = Struct
instance TransformableFbr AddX

instance Transformable AddX FbrOrt where tau Struct = Struct
instance TransformableFbrOrt AddX

instance Transformable AddX Add where tau Struct = Struct
instance TransformableAdd AddX


instance TransformableG Op AddX AddX where tauG Struct = Struct
instance TransformableOp AddX

instance Transformable AddX Typ where tau Struct = Struct

instance Transformable AddX Type where tau _ = Struct
instance TransformableType AddX

--------------------------------------------------------------------------------
-- xsoAddX

xsoAddX :: X (SomeObjectClass (SHom AddX AddX Op (HomEmpty AddX)))
xsoAddX = xOneOf [ SomeObjectClass (Struct :: Struct AddX OS)
                 , SomeObjectClass (Struct :: Struct AddX N)
                 -- , SomeObjectClass (Struct :: Struct AddX (Id OS))
                 ]
        
--------------------------------------------------------------------------------
-- prpHomDisjOpAdd -

relHomAddAddX :: (HomAdditive h, Show2 h)
  => Homomorphous AddX x y -> h x y -> Statement
relHomAddAddX (Struct :>: Struct) h
  = And [ Forall xr (prpHomAdd1 h)
        , Forall xa2 (prpHomAdd2 h)
        ]
  where XAdd _ xr _ xa2 _ = xStandardAdd
  
relHomDisjOpAdd :: X (SomeMorphism (HomDisjEmpty AddX Op)) -> Statement
relHomDisjOpAdd xsh = Forall xsh
  (\(SomeMorphism h) -> relHomAddAddX (tauHom (homomorphous h)) h)

prpHomDisjOpAdd :: Statement
prpHomDisjOpAdd = Prp "HomDisjOpAdd" :<=>: relHomDisjOpAdd xsh where
  xsh :: X (SomeMorphism (HomDisjEmpty AddX Op))
  xsh = amap1 smCmpb2 $ xscmHomDisj xsoAddX XEmpty
  
