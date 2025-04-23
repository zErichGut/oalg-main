
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
-- Module      : OAlg.Data.SDualisable
-- Description : dualisable structured types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- dualisable structured types.
module OAlg.Data.SDualisable
  (
    -- * Structural Duality
    -- ** Dualisable
    SDualisable, sdlToDual
  , SDualisableG(..), SDualityG(..)
  , SReflexiveG(..), toDualG'

    -- ** Bi-Dualisable
  , SBiDualisable, SBiDualisableG(..)

    -- * Proposition
  , prpSDualisableG

  ) where

import OAlg.Prelude

import OAlg.Data.Identity

--------------------------------------------------------------------------------
-- SReflexiveG -

-- | category equipped with a reflection.
class (Category c, TransformableG d s (ObjectClass c)) => SReflexiveG c s o d where
  reflG :: Struct s x -> Inv2 c (d x) (d (o (o x)))

--------------------------------------------------------------------------------
-- SDualisableG -

-- | duality of @__s__@-structured types given by a reflection.
--
-- __Property__ Let @'SDualisableG' __c s o d__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
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
class (SReflexiveG c s o d, Transformable1 o s) => SDualisableG c s o d where
  toDualG :: Struct s x -> c (d x) (d (o x))
  fromDualG :: Struct s x -> c (d (o x)) (d x)
  fromDualG s = v . toDualG (tau1 s) where Inv2 _ v = reflG s

--------------------------------------------------------------------------------
-- SDualityG -

-- | attest of being 'SDualisableG'.
data SDualityG c s o d where SDualityG :: SDualisableG c s o d => SDualityG c s o d

--------------------------------------------------------------------------------
-- reflG' -

-- | prefixing a proxy.
reflG' :: SDualisableG c s o d => q c s o d -> Struct s x -> Inv2 c (d x) (d (o (o x)))
reflG' _ = reflG

--------------------------------------------------------------------------------
-- toDualG' -

-- | prefixing a proxy.
toDualG' :: SDualisableG c s o d => q c s o d -> Struct s x -> c (d x) (d (o x))
toDualG' _ = toDualG

--------------------------------------------------------------------------------
-- fromDualG' -

-- | prefixing a proxy.
fromDualG' :: SDualisableG c s o d => q c s o d -> Struct s x -> c (d (o x)) (d x)
fromDualG' _ = fromDualG

--------------------------------------------------------------------------------
-- prpSDualisableG -

-- | validity according to 'SDualisableG'.
prpSDualisableG :: SDualisableG c s o d
  => EqExt c
  => q c s o d -> Struct s x -> Statement
prpSDualisableG q s = Prp "SDualisableG" :<=>:
  And [ Label "1" :<=>: (toDualG' q s' . toDualG' q s .=. u)
      , Label "2" :<=>: (toDualG' q s . v .=. v' . toDualG' q s'')
      , Label "3" :<=>: (fromDualG' q s .=. v . toDualG' q s')
      ]
  where s'        = tau1 s
        s''       = tau1 s' 
        Inv2 u v  = reflG' q s
        Inv2 _ v' = reflG' q s'

--------------------------------------------------------------------------------
-- SDualisableG - Instances -

instance SReflexiveG (->) s Op Id where
  reflG _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))
  
instance Transformable1 Op s => SDualisableG (->) s Op Id where
  toDualG _   = toIdG Op
  fromDualG _ = toIdG fromOp

--------------------------------------------------------------------------------
-- SDualisable -

-- | dualisable for the category @('->')@.
type SDualisable = SDualisableG (->)

--------------------------------------------------------------------------------
-- sdlToDual -

-- | to dual.
sdlToDual :: SDualisable s o Id => Struct s x -> x -> o x
sdlToDual s x = x' where Id x' = toDualG s (Id x)

--------------------------------------------------------------------------------
-- SBiDualisableG -

class (SReflexiveG c s o a, SReflexiveG c s o b, Transformable1 o s)
  => SBiDualisableG c s o a b where
  sdlToDualLft :: Struct s x -> c (a x) (b (o x))
  sdlToDualRgt :: Struct s x -> c (b x) (a (o x))

  sdlFromDualLft :: Struct s x -> c (b (o x)) (a x)
  sdlFromDualLft s = v . sdlToDualRgt (tau1 s) where Inv2 _ v = reflG s
  
  sdlFromDualRgt :: Struct s x -> c (a (o x)) (b x)
  sdlFromDualRgt s = v . sdlToDualLft (tau1 s) where Inv2 _ v = reflG s

--------------------------------------------------------------------------------
-- SBiDualisable -

-- | bi-dualisable for for the category @('->')@.
type SBiDualisable = SBiDualisableG (->)
