
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

-- | category @__c__@ equipped with a reflection.
class Category c => ReflexiveG c o d where
  reflG :: Struct (ObjectClass c) x -> Inv2 c (d x) (d (o (o x)))

--------------------------------------------------------------------------------
-- DualisableG -

-- | category @__c__@ equipped with a duality via a reflection.
--
-- __Property__ Let @'DualisableG' __c s o d__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
-- holds:
--
-- (1) @'toDualG'' q s' '.' 'toDualG'' q s '.=.' u@.
--
-- (2) @'toDualG'' q s '.' v '.=.' v' . 'toDualG'' q s''@.
--
-- (3) @'fromDualG'' q s '.=.' v '.' 'toDualG'' q s'@.
--
-- where @q@ is any proxy in @__q c s o d__@, @s' = 'tau1' s@ , @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'relfG'' q s@ and @'Inv2' _ v' = 'reflG'' q s'@.
--
-- __Note__ The properties above imply that @'toDualG' s@ and @'fromDualG' s@ are inverse
-- in @__c__@ for all @__x__@ and @s@ in @'Struct' __s x__@ and hence establish a duality
-- within @__s__@ structured types.
class (ReflexiveG c o d, Transformable1 o (ObjectClass c)) => DualisableG c o d where
  toDualG :: Struct (ObjectClass c) x -> c (d x) (d (o x))
  fromDualG :: Struct (ObjectClass c) x -> c (d (o x)) (d x)
  fromDualG s = v . toDualG (tau1 s) where Inv2 _ v = reflG s

--------------------------------------------------------------------------------
-- DualisableGId -

-- | helper class to avoid undecidable instances.
class DualisableG (->) o Id => DualisableGId o

--------------------------------------------------------------------------------
-- Op - SDualisable -

instance ReflexiveG (->) Op Id where
  reflG _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))

instance DualisableG (->) Op Id where
  toDualG _   = amap1 Op
  fromDualG _ = amap1 fromOp

instance DualisableGId Op

--------------------------------------------------------------------------------
-- SDualityG -

-- | attest of being 'DualisableG'.
data SDualityG c o d where SDualityG :: DualisableG c o d => SDualityG c o d

--------------------------------------------------------------------------------
-- reflG' -

-- | prefixing a proxy.
reflG' :: DualisableG c o d => q c o d -> Struct (ObjectClass c) x -> Inv2 c (d x) (d (o (o x)))
reflG' _ = reflG

--------------------------------------------------------------------------------
-- toDualG' -

-- | prefixing a proxy.
toDualG' :: DualisableG c o d => q c o d -> Struct (ObjectClass c) x -> c (d x) (d (o x))
toDualG' _ = toDualG

--------------------------------------------------------------------------------
-- fromDualG' -

-- | prefixing a proxy.
fromDualG' :: DualisableG c o d => q c o d -> Struct (ObjectClass c) x -> c (d (o x)) (d x)
fromDualG' _ = fromDualG

--------------------------------------------------------------------------------
-- prpDualisableG -

-- | validity according to 'DualisableG'.
prpDualisableG :: (DualisableG c o d, EqExt c)
  => q c o d -> Struct (ObjectClass c) x -> Statement
prpDualisableG q s = Prp "DualisableG" :<=>:
  And [ Label "1" :<=>: (toDualG' q s' . toDualG' q s .=. u)
      , Label "2" :<=>: (toDualG' q s . v .=. v' . toDualG' q s'')
      , Label "3" :<=>: (fromDualG' q s .=. v . toDualG' q s')
      ]
  where s'        = tau1 s
        s''       = tau1 s' 
        Inv2 u v  = reflG' q s
        Inv2 _ v' = reflG' q s'

--------------------------------------------------------------------------------
-- DualisableGBi -

-- | category @__c__@ equipped with a bi-duality via reflections.
class (ReflexiveG c o a, ReflexiveG c o b, Transformable1 o (ObjectClass c))
  => DualisableGBi c o a b where
  toDualGLft :: Struct (ObjectClass c) x -> c (a x) (b (o x))
  toDualGRgt :: Struct (ObjectClass c) x -> c (b x) (a (o x))

  fromDualGLft :: Struct (ObjectClass c) x -> c (b (o x)) (a x)
  fromDualGLft s = v . toDualGRgt (tau1 s) where Inv2 _ v = reflG s
  
  fromDualGRgt :: Struct (ObjectClass c) x -> c (a (o x)) (b x)
  fromDualGRgt s = v . toDualGLft (tau1 s) where Inv2 _ v = reflG s

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


