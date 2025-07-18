
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
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
    HomVectorial, DualisableVectorial

    -- * Proposition
  , prpHomVectorial, prpDualisableVectorial
  , prpHomDisjOpVecZ
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
import OAlg.Structure.Vectorial

import OAlg.Hom.Oriented
import OAlg.Hom.Fibred
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

instance ( TransformableFbr (s k)
         , TransformableAdd (s k)
         , TransformableVec k s
         )
  => HomVectorial k (IdHom (s k))

instance HomVectorial k (HomEmpty (VecX k))

--------------------------------------------------------------------------------
-- prpHomVectorial -

relHomVectorial :: HomVectorial k h
  => Homomorphous (Vec k) x y -> h x y -> k -> x -> Statement
relHomVectorial (Struct :>: Struct) h k x
  = (amap h (k ! x) == k ! amap h x) :?> Params ["k":=show k, "x":=show x]

-- | validity according to 'HomVectorial'.
prpHomVectorial :: HomVectorial k h
  => h x y -> k -> x -> Statement
prpHomVectorial h k x = Prp "HomVectorial"
  :<=>: relHomVectorial (tauHom (homomorphous h)) h k x
  
--------------------------------------------------------------------------------
-- DualisableVectorial -

-- | duality according to @__o__@ on @__k__@-'Vectorial' structures.
--
-- __Propoerty__ Let @'DualisableVectorial' __k s o__@ then for all @__x__@, @s@ in @'Struct' __s x__@
-- and @k@ in @__k__@ holds:
--
-- (1) @'toDualArw' q s (k '!' x) '==' k '!' toDualArw q s x@.
--
-- where @q@ is any proxy for @__o__@.
class (DualisableAdditive s o, Transformable s (Vec k)) => DualisableVectorial k s o

instance ( HomVectorial k h, HomFibredOriented h
         , DualisableVectorial k s o
         ) => HomVectorial k (HomDisj s o h)

--------------------------------------------------------------------------------
-- relDualisableVectorial -

relDualisableVectorial :: DualisableVectorial k s o
  => q o -> Struct s x -> Struct (Vec k) x -> Struct (Vec k) (o x) -> k -> x -> Statement
relDualisableVectorial q s Struct Struct k x
  = (toDualArw q s (k ! x) == k ! toDualArw q s x) :?> Params ["k":=show k, "x":=show x]

prpDualisableVectorial :: DualisableVectorial k s o
  => q o -> Struct s x -> k -> x -> Statement
prpDualisableVectorial q s k x = Prp "DualisableVectorial"
  :<=>: relDualisableVectorial q s (tau s) (tau (tauO s)) k x

--------------------------------------------------------------------------------
-- VecX -

data VecX k

type instance Structure (VecX k) x = ( Vectorial x, Scalar x ~ k
                                     , FibredOriented x
                                     , XStandard k, XStandard x
                                     )

instance Transformable (VecX k) Fbr where tau Struct = Struct
instance TransformableFbr (VecX k)

instance Transformable (VecX k) Add where tau Struct = Struct
instance TransformableAdd (VecX k)

instance Transformable (VecX k) (Vec k) where tau Struct = Struct

instance Transformable (VecX k) Ort where tau Struct = Struct
instance TransformableOrt (VecX k)

instance Transformable (VecX k) FbrOrt where tau Struct = Struct
instance TransformableFbrOrt (VecX k)

instance TransformableG Op (VecX k) (VecX k) where tauG Struct = Struct 
instance TransformableOp (VecX k)
instance DualisableVectorial k (VecX k) Op

instance Transformable (VecX k) Type where tau _ = Struct
instance TransformableType (VecX k)

instance Transformable (VecX k) Typ where tau Struct = Struct

relHomDisjOpVecZStruct :: HomVectorial Z h
  => Homomorphous (VecX Z) x y -> h x y -> Statement
relHomDisjOpVecZStruct (sx@Struct :>: Struct) h= Forall (xkx sx) (\(k,x) -> prpHomVectorial h k x)
  where
    xkx :: Struct (VecX k) x -> X (k,x)
    xkx Struct = xTupple2 xStandard xStandard 
                                                 

relHomDisjOpVecZ :: X (SomeMorphism (HomDisjEmpty (VecX Z) Op)) -> Statement
relHomDisjOpVecZ xsh = Forall xsh
  (\(SomeMorphism h) -> relHomDisjOpVecZStruct (tauHom (homomorphous h)) h)

prpHomDisjOpVecZ :: Statement
prpHomDisjOpVecZ = Prp "HomDisjOpVecZ" :<=>: relHomDisjOpVecZ xsh where
  xsh :: X (SomeMorphism (HomDisjEmpty (VecX Z) Op))
  xsh = amap1 smCmpb2 $ xscmHomDisj xsoVecXZ XEmpty

--------------------------------------------------------------------------------
-- xsoVecXZ -

xsoVecXZ :: s ~ VecX Z => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoVecXZ = xOneOf [ SomeObjectClass (Struct :: Struct (VecX Z) (ZMod Z))
                  , SomeObjectClass (Struct :: Struct (VecX Z) (ZMod Q))
                  , SomeObjectClass (Struct :: Struct (VecX Z) (ZMod OS))
                  ]

--------------------------------------------------------------------------------
-- ZMod -

newtype ZMod x = ZMod x deriving (Eq,Show,Validable)

instance XStandard x => XStandard (ZMod x) where xStandard = amap1 ZMod xStandard

type instance Point (ZMod x) = Point x
instance ShowPoint x => ShowPoint (ZMod x)
instance EqPoint x => EqPoint (ZMod x)
instance ValidablePoint x => ValidablePoint (ZMod x)
instance TypeablePoint x => TypeablePoint (ZMod x)

instance Oriented x => Oriented (ZMod x) where
  orientation (ZMod x) = orientation x

type instance Root (ZMod x) = Root x
instance ShowRoot x => ShowRoot (ZMod x)
instance EqRoot x => EqRoot (ZMod x)
instance ValidableRoot x => ValidableRoot (ZMod x)
instance TypeableRoot x => TypeableRoot (ZMod x)

instance FibredOriented x => Fibred (ZMod x)
instance FibredOriented x => FibredOriented (ZMod x)

instance (Additive x, FibredOriented x) => Additive (ZMod x) where
  zero r = ZMod (zero r)
  ZMod a + ZMod b = ZMod (a+b)
  ntimes n (ZMod a) = ZMod (ntimes n a)

instance (Abelian x, FibredOriented x) => Abelian (ZMod x) where
  negate (ZMod x) = ZMod (negate x)
  ZMod a - ZMod b = ZMod (a-b)
  ztimes z (ZMod a) = ZMod (ztimes z a)

instance (Abelian x, FibredOriented x) => Vectorial (ZMod x) where
  type Scalar (ZMod x) = Z
  (!) = ztimes

