
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
-- Module      : OAlg.Category.DualisableG
-- Description : generalized duality for categories.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- generalized duality for categories.
module OAlg.Category.DualisableG
  (
    -- * Structural Duality
    -- ** Dualisable
    DualisableG(..), SDualityG(..)
  , DualisableGId
  , ReflexiveG(..), reflG'
  , toDualG'

    -- ** Bi-Dualisable
  , DualisableGBi(..)

    -- * SDual
  , SDual(..), fromSDual, mapSDual
    -- * Proposition
  , prpDualisableG

  ) where

import OAlg.Category.Definition

import OAlg.Data.Identity
import OAlg.Data.Opposite
import OAlg.Data.Dualisable
import OAlg.Data.EqualExtensional
import OAlg.Data.Statement.Definition

import OAlg.Structure.Definition


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
-- @'Inv2' u v = 'relfG'' q r@ and @'Inv2' _ v' = 'reflG'' q r'@.
--
-- __Note__ The properties above imply that @'toDualG' r@ and @'fromDualG' r@ are inverse
-- in @__c__@ for all @__x__@ and @r@ in @'Struct' __r x__@ and hence establish a duality
-- within @__r__@ structured types.
class (ReflexiveG r c o d, Transformable1 o r) => DualisableG r c o d where
  toDualG :: Struct r x -> c (d x) (d (o x))
  fromDualG :: Struct r x -> c (d (o x)) (d x)
  fromDualG r = v . toDualG (tau1 r) where Inv2 _ v = reflG r

--------------------------------------------------------------------------------
-- DualisableGId -

-- | helper class to avoid undecidable instances.
class DualisableG r (->) o Id => DualisableGId r o

--------------------------------------------------------------------------------
-- Op - SDualisable -

instance ReflexiveG r (->) Op Id where
  reflG _ = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))

instance TransformableOp r => DualisableG r (->) Op Id where
  toDualG _   = amap1 Op
  fromDualG _ = amap1 fromOp

instance TransformableOp r => DualisableGId r Op

--------------------------------------------------------------------------------
-- SDualityG -

-- | attest of being 'DualisableG'.
data SDualityG r c o d where SDualityG :: DualisableG r c o d => SDualityG r c o d

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
-- DualisableGBi -

-- | category @__c__@ equipped with a bi-duality via reflections.
class (ReflexiveG r c o a, ReflexiveG r c o b, Transformable1 o r)
  => DualisableGBi r c o a b where
  toDualGLft :: Struct r x -> c (a x) (b (o x))
  toDualGRgt :: Struct r x -> c (b x) (a (o x))

  fromDualGLft :: Struct r x -> c (b (o x)) (a x)
  fromDualGLft r = v . toDualGRgt (tau1 r) where Inv2 _ v = reflG r
  
  fromDualGRgt :: Struct r x -> c (a (o x)) (b x)
  fromDualGRgt r = v . toDualGLft (tau1 r) where Inv2 _ v = reflG r

--------------------------------------------------------------------------------
-- SDual -

-- | wrapper for @'Dual1' __d x__@.
newtype SDual d x = SDual (Dual1 d x)

--------------------------------------------------------------------------------
-- fromSDual -

-- | deconstructing 'SDual'
fromSDual :: SDual d x -> Dual1 d x
fromSDual (SDual d) = d

--------------------------------------------------------------------------------
-- mapSDual -

-- | mapping 'SDual'.
mapSDual :: (Dual1 d x -> Dual1 d y) -> SDual d x -> SDual d y
mapSDual f (SDual x) = SDual (f x)

