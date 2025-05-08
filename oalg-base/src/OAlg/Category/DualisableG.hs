

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
    SDualisable
  , SDualisableG(..), SDualityG(..)
  , SDualisableGId --, SDualisableGPnt
  , SReflexiveG(..), sdlRefl'
  , sdlToDual'

    -- ** Bi-Dualisable
  , SBiDualisable, SBiDualisableG(..)

    -- * SDual
  , SDual(..), fromSDual, mapSDual
    -- * Proposition
  , prpSDualisableG

    
  ) where

import OAlg.Category.Definition

import OAlg.Data.Identity
import OAlg.Data.Opposite
import OAlg.Data.Dualisable
import OAlg.Data.EqualExtensional
import OAlg.Data.Statement.Definition

import OAlg.Structure.Definition


--------------------------------------------------------------------------------
-- SReflexiveG -

-- | category @__c__@ equipped with a reflection on the sub set of its object class given by @__s__@. 
class Category c => SReflexiveG c o d where
  sdlRefl :: Struct (ObjectClass c) x -> Inv2 c (d x) (d (o (o x)))

--------------------------------------------------------------------------------
-- SDualisableG -

-- | duality of @__s__@-structured types given by a reflection.
--
-- __Property__ Let @'SDualisableG' __c s o d__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
-- holds:
--
-- (1) @'sdlToDual'' q s' '.' 'sdlToDual'' q s '.=.' u@.
--
-- (2) @'sdlToDual'' q s '.' v '.=.' v' . 'sdlToDual'' q s''@.
--
-- (3) @'sdlFromDual'' q s '.=.' v '.' 'sdlToDual'' q s'@.
--
-- where @q@ is any proxy in @__q c s o d__@, @s' = 'tau1' s@ , @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'relfG'' q s@ and @'Inv2' _ v' = 'sdlRefl'' q s'@.
--
-- __Note__ The properties above imply that @'sdlToDual' s@ and @'sdlFromDual' s@ are inverse
-- in @__c__@ for all @__x__@ and @s@ in @'Struct' __s x__@ and hence establish a duality
-- within @__s__@ structured types.
class (SReflexiveG c o d, Transformable1 o (ObjectClass c)) => SDualisableG c o d where
  sdlToDual :: Struct (ObjectClass c) x -> c (d x) (d (o x))
  sdlFromDual :: Struct (ObjectClass c) x -> c (d (o x)) (d x)
  sdlFromDual s = v . sdlToDual (tau1 s) where Inv2 _ v = sdlRefl s

--------------------------------------------------------------------------------
-- SDualisableGId -

-- | helper class to avoid undecidable instances.
class SDualisableG (->) o Id => SDualisableGId o

--------------------------------------------------------------------------------
-- Op - SDualisable -

instance SReflexiveG (->) Op Id where
  sdlRefl _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))

instance SDualisableG (->) Op Id where
  sdlToDual _   = amap1 Op
  sdlFromDual _ = amap1 fromOp

instance SDualisableGId Op

--------------------------------------------------------------------------------
-- SDualityG -

-- | attest of being 'SDualisableG'.
data SDualityG c o d where SDualityG :: SDualisableG c o d => SDualityG c o d


--------------------------------------------------------------------------------
-- sdlRefl' -

-- | prefixing a proxy.
sdlRefl' :: SDualisableG c o d => q c o d -> Struct (ObjectClass c) x -> Inv2 c (d x) (d (o (o x)))
sdlRefl' _ = sdlRefl

--------------------------------------------------------------------------------
-- sdlToDual' -

-- | prefixing a proxy.
sdlToDual' :: SDualisableG c o d => q c o d -> Struct (ObjectClass c) x -> c (d x) (d (o x))
sdlToDual' _ = sdlToDual

--------------------------------------------------------------------------------
-- sdlFromDual' -

-- | prefixing a proxy.
sdlFromDual' :: SDualisableG c o d => q c o d -> Struct (ObjectClass c) x -> c (d (o x)) (d x)
sdlFromDual' _ = sdlFromDual

--------------------------------------------------------------------------------
-- prpSDualisableG -

-- | validity according to 'SDualisableG'.
prpSDualisableG :: (SDualisableG c o d, EqExt c)
  => q c o d -> Struct (ObjectClass c) x -> Statement
prpSDualisableG q s = Prp "SDualisableG" :<=>:
  And [ Label "1" :<=>: (sdlToDual' q s' . sdlToDual' q s .=. u)
      , Label "2" :<=>: (sdlToDual' q s . v .=. v' . sdlToDual' q s'')
      , Label "3" :<=>: (sdlFromDual' q s .=. v . sdlToDual' q s')
      ]
  where s'        = tau1 s
        s''       = tau1 s' 
        Inv2 u v  = sdlRefl' q s
        Inv2 _ v' = sdlRefl' q s'

--------------------------------------------------------------------------------
-- SDualisable -

-- | dualisable for the category @('->')@.
type SDualisable = SDualisableG (->)

--------------------------------------------------------------------------------
-- SBiDualisableG -

class (SReflexiveG c o a, SReflexiveG c o b, Transformable1 o (ObjectClass c))
  => SBiDualisableG c o a b where
  sdlToDualLft :: Struct (ObjectClass c) x -> c (a x) (b (o x))
  sdlToDualRgt :: Struct (ObjectClass c) x -> c (b x) (a (o x))

  sdlFromDualLft :: Struct (ObjectClass c) x -> c (b (o x)) (a x)
  sdlFromDualLft s = v . sdlToDualRgt (tau1 s) where Inv2 _ v = sdlRefl s
  
  sdlFromDualRgt :: Struct (ObjectClass c) x -> c (a (o x)) (b x)
  sdlFromDualRgt s = v . sdlToDualLft (tau1 s) where Inv2 _ v = sdlRefl s

--------------------------------------------------------------------------------
-- SBiDualisable -

-- | bi-dualisable for for the category @('->')@.
type SBiDualisable = SBiDualisableG (->)

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


