
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , ConstraintKinds
#-}

-- |
-- Module      : OAlg.Category.Dualisable
-- Description : generalized duality for categories.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- generalized duality for categories.
module OAlg.Category.Dualisable
  (
    -- * Dualisable
    DualisableG(..), DualityG(..)
  , DualisableGId, DualisableGPnt
  
  , ReflexiveG(..), reflG'
  , toDualG'
  , tauO

  
    -- * Dualisable Pairing
  , DualisableGPair(..), DualisableGBi

    -- * Proposition
  , prpDualisableG

  ) where

import Data.Kind

import OAlg.Category.Definition
import OAlg.Data.Identity

import OAlg.Data.Dualisable
import OAlg.Data.EqualExtensional
import OAlg.Data.Statement.Definition

import OAlg.Structure.Definition
import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented

--------------------------------------------------------------------------------
-- tauO -

-- | propagating the @__s__@ structure to @__o__@.
tauO :: Transformable1 o s => Struct s x -> Struct s (o x)
tauO = tauG

--------------------------------------------------------------------------------
-- ReflexiveG -

-- | category @__c__@ equipped with a reflection on a subset of @'ObjectClass' __c__@ given by @__r__@.
class (Category c, Transformable r (ObjectClass c)) => ReflexiveG r c o d where
  reflG :: Struct r x -> Inv2 c (d x) (d (o (o x)))

--------------------------------------------------------------------------------
-- DualisableG -

-- | category @__c__@ equipped with a duality via a reflection.
--
-- __Property__ Let @'DualisableG' __r c o d__@, then for all @__x__@ and @r@ in @'Struct' __r x__@
-- holds:
--
-- (1) @'toDualG'' q r' '.' 'toDualG'' q r '.=.' u@.
--
-- (2) @'toDualG'' q r '.' v '.=.' v' . 'toDualG'' q r''@.
--
-- (3) @'fromDualG'' q r '.=.' v '.' 'toDualG'' q r'@.
--
-- where @q@ is any proxy in @__q c o d__@, @r' = 'tau1' r@ , @r'' = 'tau1' r'@,
-- @'Inv2' u v = 'reflG'' q r@ and @'Inv2' _ v' = 'reflG'' q r'@.
--
-- __Note__ The properties above imply that @'toDualG' r@ and @'fromDualG' r@ are inverse
-- in @__c__@ for all @__x__@ and @r@ in @'Struct' __r x__@ and hence establish a duality
-- within @__r__@ structured types.
class (ReflexiveG r c o d, Transformable1 o r) => DualisableG r c o d where
  toDualG :: Struct r x -> c (d x) (d (o x))
  fromDualG :: Struct r x -> c (d (o x)) (d x)
  fromDualG r = v . toDualG (tau1 r) where Inv2 _ v = reflG r

-- | helper class to avoid undecidable instances.
class DualisableG r (->) o Id => DualisableGId r o

-- | helper class to avoid undecidable instances.
class DualisableG r (->) o Pnt => DualisableGPnt r o

--------------------------------------------------------------------------------
-- DualityG -

-- | attest of being 'DualisableG'.
data DualityG r c o d where DualityG :: DualisableG r c o d => DualityG r c o d

--------------------------------------------------------------------------------
-- reflG' -

-- | prefixing a proxy.
reflG' :: ReflexiveG r c o d => q c o d -> Struct r x -> Inv2 c (d x) (d (o (o x)))
reflG' _ = reflG

--------------------------------------------------------------------------------
-- toDualG' -

-- | prefixing a proxy.
toDualG' :: DualisableG r c o d => q c o d -> Struct r x -> c (d x) (d (o x))
toDualG' _ = toDualG

--------------------------------------------------------------------------------
-- fromDualG' -

-- | prefixing a proxy.
fromDualG' :: DualisableG r c o d => q c o d -> Struct r x -> c (d (o x)) (d x)
fromDualG' _ = fromDualG

--------------------------------------------------------------------------------
-- prpDualisableG -

-- | validity according to 'DualisableG'.
prpDualisableG :: (DualisableG r c o d, EqExt c)
  => q c o d -> Struct r x -> Statement
prpDualisableG q r = Prp "DualisableG" :<=>:
  And [ Label "1" :<=>: (toDualG' q r' . toDualG' q r .=. u)
      , Label "2" :<=>: (toDualG' q r . v .=. v' . toDualG' q r'')
      , Label "3" :<=>: (fromDualG' q r .=. v . toDualG' q r')
      ]
  where r'        = tau1 r
        r''       = tau1 r' 
        Inv2 u v  = reflG' q r
        Inv2 _ v' = reflG' q r'

--------------------------------------------------------------------------------
-- DualisableGPair -

-- | category @__c__@ equipped with a duality pairing between @__a__@ and @__b__@ via reflections.
class (ReflexiveG r c o a, ReflexiveG r c o b, Transformable1 o r)
  => DualisableGPair r c o a b where
  toDualGLft :: Struct r x -> c (a x) (b (o x))
  toDualGRgt :: Struct r x -> c (b x) (a (o x))

  fromDualGLft :: Struct r x -> c (b (o x)) (a x)
  fromDualGLft r = v . toDualGRgt (tau1 r) where Inv2 _ v = reflG r
  
  fromDualGRgt :: Struct r x -> c (a (o x)) (b x)
  fromDualGRgt r = v . toDualGLft (tau1 r) where Inv2 _ v = reflG r

--------------------------------------------------------------------------------
-- DualisableGBi -

-- | category @__c__@ equipped with a duality pairing between @__d__@ and its dual @'Dual1' __d__@
-- via reflections.
class DualisableGPair r c o d (Dual1 d) => DualisableGBi r c o d

--------------------------------------------------------------------------------
-- Op - DualisableG - Id -

instance Transformable r Type => ReflexiveG r (->) Op Id where
  reflG _ = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))

instance (Transformable r Type, TransformableOp r) => DualisableG r (->) Op Id where
  toDualG _   = amap1 Op
  fromDualG _ = amap1 fromOp

instance (TransformableType r, TransformableOp r) => DualisableGId r Op

instance ReflexiveG OrtX EqualExtOrt Op Id where
  reflG r@Struct = Inv2 (Sub u) (Sub v) where Inv2 u v = reflG r

instance DualisableG OrtX EqualExtOrt Op Id where
  toDualG r@Struct = Sub t where t = toDualG r

--------------------------------------------------------------------------------
-- Op - DualisableG - Pnt -

instance Transformable r Type => ReflexiveG r (->) Op Pnt where
  reflG _ = Inv2 idPnt idPnt where
    
instance (Transformable r Type, TransformableOp r) => DualisableG r (->) Op Pnt where
  toDualG _   = idPnt
  fromDualG _ = idPnt

instance (TransformableType r, TransformableOp r) => DualisableGPnt r Op

instance ReflexiveG OrtX EqualExtOrt Op Pnt where
  reflG r@Struct = Inv2 (Sub u) (Sub v) where Inv2 u v = reflG r

instance DualisableG OrtX EqualExtOrt Op Pnt where
  toDualG r@Struct = Sub t where t = toDualG r 

--------------------------------------------------------------------------------
-- toDualRtOp -

-- | the dual root for on 'FibredOriented'-structures.
toDualRtOp :: Struct FbrOrt x -> Rt x -> Rt (Op x)
toDualRtOp Struct (Rt r) = Rt (opposite r)

--------------------------------------------------------------------------------
-- Op - DualisableG - Rt -

instance Transformable r Type => ReflexiveG r (->) Op Rt where
  reflG _ = Inv2 idRt idRt

instance (Transformable r Type, TransformableOp r, Transformable r FbrOrt)
  => DualisableG r (->) Op Rt where
  toDualG s = toDualRtOp (tau s)


