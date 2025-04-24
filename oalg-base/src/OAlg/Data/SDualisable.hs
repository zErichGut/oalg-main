
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
    SDualisable
  , SDualisableG(..), SDualityG(..)
  , SReflexiveG(..), sdlToDual'

    -- ** Bi-Dualisable
  , SBiDualisable, SBiDualisableG(..)

    -- * Proposition
  , prpSDualisableG

  ) where

import OAlg.Prelude

import OAlg.Data.Identity

import OAlg.Structure.Oriented.Definition

--------------------------------------------------------------------------------
-- SReflexiveG -

-- | category equipped with a reflection.
class (Category c, TransformableG d s (ObjectClass c)) => SReflexiveG c s o d where
  sdlRefl :: Struct s x -> Inv2 c (d x) (d (o (o x)))

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
class (SReflexiveG c s o d, Transformable1 o s) => SDualisableG c s o d where
  sdlToDual :: Struct s x -> c (d x) (d (o x))
  sdlFromDual :: Struct s x -> c (d (o x)) (d x)
  sdlFromDual s = v . sdlToDual (tau1 s) where Inv2 _ v = sdlRefl s

--------------------------------------------------------------------------------
-- SDualityG -

-- | attest of being 'SDualisableG'.
data SDualityG c s o d where SDualityG :: SDualisableG c s o d => SDualityG c s o d

--------------------------------------------------------------------------------
-- sdlRefl' -

-- | prefixing a proxy.
sdlRefl' :: SDualisableG c s o d => q c s o d -> Struct s x -> Inv2 c (d x) (d (o (o x)))
sdlRefl' _ = sdlRefl

--------------------------------------------------------------------------------
-- sdlToDual' -

-- | prefixing a proxy.
sdlToDual' :: SDualisableG c s o d => q c s o d -> Struct s x -> c (d x) (d (o x))
sdlToDual' _ = sdlToDual

--------------------------------------------------------------------------------
-- sdlFromDual' -

-- | prefixing a proxy.
sdlFromDual' :: SDualisableG c s o d => q c s o d -> Struct s x -> c (d (o x)) (d x)
sdlFromDual' _ = sdlFromDual

--------------------------------------------------------------------------------
-- prpSDualisableG -

-- | validity according to 'SDualisableG'.
prpSDualisableG :: SDualisableG c s o d
  => EqExt c
  => q c s o d -> Struct s x -> Statement
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
-- SDualisableG - Instances -

instance SReflexiveG (->) s Op Id where
  sdlRefl _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))
  
instance Transformable1 Op s => SDualisableG (->) s Op Id where
  sdlToDual _   = toIdG Op
  sdlFromDual _ = toIdG fromOp

idPnt :: Point x ~ Point y => Pnt x -> Pnt y
idPnt (Pnt p) = Pnt p
  
instance SReflexiveG (->) s Op Pnt where
  sdlRefl _ = Inv2 idPnt idPnt where
    
instance Transformable1 Op s => SDualisableG (->) s Op Pnt where
  sdlToDual _ = idPnt 

--------------------------------------------------------------------------------
-- SDualisable -

-- | dualisable for the category @('->')@.
type SDualisable = SDualisableG (->)

--------------------------------------------------------------------------------
-- SBiDualisableG -

class (SReflexiveG c s o a, SReflexiveG c s o b, Transformable1 o s)
  => SBiDualisableG c s o a b where
  sdlToDualLft :: Struct s x -> c (a x) (b (o x))
  sdlToDualRgt :: Struct s x -> c (b x) (a (o x))

  sdlFromDualLft :: Struct s x -> c (b (o x)) (a x)
  sdlFromDualLft s = v . sdlToDualRgt (tau1 s) where Inv2 _ v = sdlRefl s
  
  sdlFromDualRgt :: Struct s x -> c (a (o x)) (b x)
  sdlFromDualRgt s = v . sdlToDualLft (tau1 s) where Inv2 _ v = sdlRefl s

--------------------------------------------------------------------------------
-- SBiDualisable -

-- | bi-dualisable for for the category @('->')@.
type SBiDualisable = SBiDualisableG (->)
