
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , TypeOperators
  , DataKinds
  , RankNTypes
  , PolyKinds
  , GeneralizedNewtypeDeriving
  , DefaultSignatures
  , FunctionalDependencies
#-}

-- |
-- Module      : OAlg.Data.SDualisable
-- Description : duality on structural data.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Duality on structural data.
module OAlg.Data.SDualisable
  (
{-
    -- * Structural Duality
    SDualisable(..), sdlTau

    -- * Structural Duality 1
  , SDualisable1(..), sdlRefl1, sdlTau1

    -- * Reflexivity
  , SReflexive(..)

    -- * Proposition
  , prpSDualisable
  , prpSDualisable1
-}
  ) where

import Data.Typeable
import Data.List ((++))

import OAlg.Category.Path

import OAlg.Data.Either

import OAlg.Prelude

--------------------------------------------------------------------------------
-- MapO -

-- | adjoining to a type family of morphisms 'ToDual' and 'FromDual'.
data MapO s o h x y where
  MapO     :: Transformable (ObjectClass h) s => h x y -> MapO s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => MapO s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => MapO s o h (o x) x

instance Transformable s Typ => TransformableObjectClassTyp (MapO s o h)
  
--------------------------------------------------------------------------------
-- MapO - Entity2 -

instance Show2 h => Show2 (MapO s o h) where
  show2 (MapO h)  = "MapO (" ++ show2 h ++ ")"
  show2 ToDual    = "ToDual"
  show2 FromDual  = "FromDual"

instance Eq2 h => Eq2 (MapO s o h) where
  eq2 (MapO f) (MapO g) = eq2 f g
  eq2 ToDual ToDual     = True
  eq2 FromDual FromDual = True
  eq2 _ _               = False

instance Validable2 h => Validable2 (MapO s o h) where
  valid2 (MapO h) = valid2 h
  valid2 _        = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (MapO s o h)

--------------------------------------------------------------------------------
-- MapO - Morphism -

instance Morphism h => Morphism (MapO s o h) where
  type ObjectClass (MapO s o h) = s

  homomorphous (MapO h) = tauHom (homomorphous h)
  homomorphous ToDual    = Struct :>: Struct
  homomorphous FromDual  = Struct :>: Struct

--------------------------------------------------------------------------------
-- MapO - Applicative -

instance (Morphism h, Applicative h, SDualisable s o) => Applicative (MapO s o h) where
  amap (MapO h)   = amap h
  amap t@ToDual   = sdlToDual (domain t)
  amap f@FromDual = sdlFromDual (range f)

----------------------------------------
-- MapO - Applicative1 -

instance (Morphism h, Applicative1 h (Either1 a b), SDualisable1 s o a b)
  => Applicative1 (MapO s o h) (Either1 a b) where
  amap1 (MapO h)   = amap1 h
  amap1 t@ToDual   = \ab -> case ab of
    Left1 a  -> Right1 $ sdlToDualLeft (domain t) a
    Right1 b -> Left1 $ sdlToDualRight (domain t) b
  amap1 f@FromDual = \ab -> case ab of
    Left1 a  -> Right1 $ sdlFromDualLeft (range f) a
    Right1 b -> Left1 $ sdlFromDualRight (range f) b

--------------------------------------------------------------------------------
-- MapOPath -

type MapOPath s o h = Path (MapO s o h)

--------------------------------------------------------------------------------
-- SReflexive -

-- | duality of @__s__@-structured types given by a reflection.
--
-- __Property__ Let @'SReflexive' __s o__@, then for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy in @__q o__@, @s' = 'tau1' s@ and @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'sdlRelf'' q s@ and @'Inv2' _ v' = 'sdlRefl'' q s'@ in
--
-- (1) @'sdlCo'' q s' '.' 'sdlCo'' q s '.=.' u@.
--
-- (2) @'sdlCo'' q s '.' v '.=.' v' . 'sdlCo'' q s''@.
class Transformable1 o s => SReflexive s o where
  sdlCo   :: Struct s x -> x -> o x
  sdlRefl :: Struct s x -> Inv2 (->) x (o (o x))

--------------------------------------------------------------------------------
-- sldCo' -

-- | prefixing a proxy.
sdlCo' :: SReflexive s o => q o -> Struct s x -> x -> o x
sdlCo' _ = sdlCo

--------------------------------------------------------------------------------
-- sdlRefl' -

-- | prefixing a proxy.
sdlRefl' :: SReflexive s o => q o -> Struct s x -> Inv2 (->) x (o (o x))
sdlRefl' _ = sdlRefl

--------------------------------------------------------------------------------
-- prpSReflexive -

-- | validity according to 'SReflexion'.
prpSReflexive :: SReflexive s o
  => (Show x, Eq x, XStandard x)
  => (Eq (o x))
  => (Show (o (o x)), Eq (o (o x)), XStandard (o (o x)))
  => q o -> Struct s x -> Statement
prpSReflexive q s = Prp "SReflexive" :<=>:
  And [ Label "sdlRefl" :<=>: prpInv2Type (Inv2 u v)
      , Label "1" :<=>: (sdlCo' q s' . sdlCo' q s .=. u)
      , Label "2" :<=>: (sdlCo' q s . v .=. v' . sdlCo' q s'')
      ]
  where s'        = tau1 s
        s''       = tau1 s'
        Inv2 u v  = sdlRefl' q s
        Inv2 _ v' = sdlRefl' q s'

--------------------------------------------------------------------------------
-- SDualisable -

-- | duality of @__s__@-structured types.
--
-- __Property__ Let @'SDualisable' __s o__@, then for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy of @__q o__@ in
--
-- (1) @'Inv2' ('sdlFromDual'' q s) ('sdlToDual'' q s)@ is 'valid'.
--
-- __Note__ If a implementation of 'SDualisable' is given by the default implemetation via 'SReflexive'
-- then holds: The property 1 above follows from the property 1 and 2 of 'SReflextion' and the
-- validity of 'sdlRefl'.
class SDualisable s o where
  sdlToDual :: Struct s x -> x -> o x
  default sdlToDual :: SReflexive s o => Struct s x -> x -> o x
  sdlToDual = sdlCo

  sdlFromDual :: Struct s x -> o x -> x
  default sdlFromDual :: SReflexive s o => Struct s x -> o x -> x
  sdlFromDual s = v . sdlCo (tau1 s) where Inv2 _ v = sdlRefl s

instance SDualisable s Op where
  sdlToDual _   = Op
  sdlFromDual _ = fromOp

--------------------------------------------------------------------------------
-- sdlToDual' -

-- | prefixing a proxy.
sdlToDual' :: SDualisable s o => q o -> Struct s x -> x -> o x
sdlToDual' _ = sdlToDual

--------------------------------------------------------------------------------
-- sdlFromDual' -

-- | prefixing a proxy.
sdlFromDual' :: SDualisable s o => q o ->  Struct s x -> o x -> x
sdlFromDual' _ = sdlFromDual

--------------------------------------------------------------------------------
-- prpSDualisable -

-- | validity accoriding to 'SDualisable'.
prpSDualisable :: SDualisable s o
  => (Show x, Eq x, XStandard x)
  => (Show (o x), Eq (o x), XStandard (o x))
  => q o
  -> Struct s x -> Statement
prpSDualisable q s = Prp "SDualisable" :<=>:
  Label "1" :<=>: prpInv2Type (Inv2 (sdlFromDual' q s) (sdlToDual' q s))


--------------------------------------------------------------------------------
-- SReflexive1 -

-- | duality of 1-parameterized types over @__s__@-structured types given by reflections.
--
-- __Property__ Let @'SReflexive' __s o a b__@, then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy in @__q o__@, @s' = 'tau1' s@ and @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'sdlRelf'' q s@ and @'Inv2' _ v' = 'sdlRefl'' q s'@ in
--
-- (1) @'sdlCoRight'' q s' '.' 'sdlCoLeft'' q s '.=.' uLeft@.
--
-- (2) @'sdlCoLeft'' q s' '.' sdlCoRight' q s '.=.' uRight@.
--
-- (3) @'sdlCoLeft'' q s '.' vLeft '.=.' vRight' '.' sdlCoLeft' q s''@.
--
-- (4) @'sdlCoRight'' q s '.' vRight '.=.' vLeft' '.' sdlCoRight' q s''@.
class Transformable1 o s => SReflexive1 s o a b | a -> b, b -> a where
  sdlCoLeft  :: Struct s x -> a x -> b (o x)
  sdlCoRight :: Struct s x -> b x -> a (o x)
  sdlReflLeft :: Struct s x -> Inv2 (->) (a x) (a (o (o x)))
  sdlReflRight :: Struct s x -> Inv2 (->) (b x) (b (o (o x)))

--------------------------------------------------------------------------------
-- sdlCoLeft' -

-- | prefixing a proxy.
sdlCoLeft' :: SReflexive1 s o a b => q o a b -> Struct s x -> a x -> b (o x)
sdlCoLeft' _ = sdlCoLeft

--------------------------------------------------------------------------------
-- sdlCoRight' -

-- | prefixing a proxy.
sdlCoRight' ::SReflexive1 s o a b => q o a b -> Struct s x -> b x -> a (o x)
sdlCoRight' _ = sdlCoRight

--------------------------------------------------------------------------------
-- sdlReflLeft' -

-- | prefixing a proxy.
sdlReflLeft' :: SReflexive1 s o a b => q o a b -> Struct s x -> Inv2 (->) (a x) (a (o (o x)))
sdlReflLeft' _ = sdlReflLeft

--------------------------------------------------------------------------------
-- sdlReflRight' -

-- | prefixing a proxy.
sdlReflRight' :: SReflexive1 s o a b => q o a b -> Struct s x -> Inv2 (->) (b x) (b (o (o x)))
sdlReflRight' _ = sdlReflRight

--------------------------------------------------------------------------------
-- prpReflexive1 -

-- | validity accoriding to 'SReflexive1'.
prpReflexive1 :: SReflexive1 s o a b
  => (Show (a x), XStandard (a x))
  => (Eq (a (o x)))
  => (Show (a (o (o x))), Eq (a (o (o x))), XStandard (a (o (o x))))
  => (Show (b x), XStandard (b x))
  => (Eq (b (o x)))
  => (Show (b (o (o x))), Eq (b (o (o x))), XStandard (b (o (o x))))
  => q o a b -> Struct s x -> Statement
prpReflexive1 q s = Prp "Reflexive1" :<=>:
  And [ Label "1" :<=>: (sdlCoRight' q s' . sdlCoLeft' q s .=. uLeft)
      , Label "2" :<=>: (sdlCoLeft' q s' . sdlCoRight' q s .=. uRight)
      , Label "3" :<=>: (sdlCoLeft' q s . vLeft .=. vRight' . sdlCoLeft' q s'')
      , Label "4" :<=>: (sdlCoRight' q s . vRight .=. vLeft' . sdlCoRight' q s'')
      ]  
  where s'  = tau1 s
        s'' = tau1 s'
        Inv2 uLeft vLeft = sdlReflLeft' q s
        Inv2 _ vLeft' = sdlReflLeft' q s'
        Inv2 uRight vRight = sdlReflRight' q s
        Inv2 _ vRight' = sdlReflRight' q s'

--------------------------------------------------------------------------------
-- SDualisable1 -

-- | duality of 1-parameterized types over @__s__@-structured types.
--
-- __Properties__ Let @'SDualisable' __s o a b__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
-- holds: Let @q@ be any proxy of @__q o a b__@ in
--
-- (1) @'Inv2' ('sdlFromDualRight'' q s) ('sdlToDualLeft'' q s)@ is 'valid'.
--
-- (2) @'Inv2' ('sdlFromDualLeft'' q s) ('sdlToDualRight'' q s)@ is 'valid'.
class SDualisable1 s o a b where
  -- | mapping to the dual of @__a__@.
  sdlToDualLeft :: Struct s x -> a x -> b (o x)
  default sdlToDualLeft :: SReflexive1 s o a b => Struct s x -> a x -> b (o x)
  sdlToDualLeft = sdlCoLeft

  -- | mapping from the dual of @__b__@.
  sdlFromDualRight :: Struct s x -> b (o x) -> a x
  default sdlFromDualRight :: SReflexive1 s o a b => Struct s x -> b (o x) -> a x
  sdlFromDualRight s = v . sdlCoRight (tau1 s) where Inv2 _ v = sdlReflLeft s

  -- | mapping to the dual of @__b__@.
  sdlToDualRight :: Struct s x -> b x -> a (o x)
  default sdlToDualRight :: SReflexive1 s o a b => Struct s x -> b x -> a (o x) 
  sdlToDualRight = sdlCoRight

  -- | mapping from the dual of @__a__@.
  sdlFromDualLeft :: Struct s x -> a (o x) -> b x
  default sdlFromDualLeft :: SReflexive1 s o a b => Struct s x -> a (o x) -> b x 
  sdlFromDualLeft s = v . sdlCoLeft (tau1 s) where Inv2 _ v = sdlReflRight s 

--------------------------------------------------------------------------------
-- sdlToDualLeft' -

-- | prefixing a proxy.
sdlToDualLeft' :: SDualisable1 s o a b => q o a b -> Struct s x -> a x -> b (o x)
sdlToDualLeft' _ = sdlToDualLeft

--------------------------------------------------------------------------------
-- sdlFromDualRigth' -

-- | prefixing a proxy.
sdlFromDualRight' :: SDualisable1 s o a b => q o a b -> Struct s x -> b (o x) -> a x
sdlFromDualRight' _ = sdlFromDualRight

--------------------------------------------------------------------------------
-- sdlToDualRigth' -

-- | prefixing a proxy.
sdlToDualRight' :: SDualisable1 s o a b => q o a b -> Struct s x -> b x -> a (o x)
sdlToDualRight' _ = sdlToDualRight

--------------------------------------------------------------------------------
-- sdlFromDualLeft'

-- | prefixing a proxy.
sdlFromDualLeft' :: SDualisable1 s o a b => q o a b -> Struct s x -> a (o x) -> b x
sdlFromDualLeft' _ = sdlFromDualLeft

--------------------------------------------------------------------------------
-- prpSDualisable1 -

-- | validity according to 'SDualisable1'.
prpSDualisable1 :: SDualisable1 s o a b
  => (Show (a x), Eq (a x), XStandard (a x))
  => (Show (b x), Eq (b x), XStandard (b x))
  => (Show (b (o x)), Eq (b (o x)), XStandard (b (o x)))
  => (Show (a (o x)), Eq (a (o x)), XStandard (a (o x)))
  => q o a b -> Struct s x -> Statement
prpSDualisable1 q s = Prp "SDualisable1" :<=>:
  And [ Label "1" :<=>: prpInv2Type (Inv2 (sdlFromDualRight' q s) (sdlToDualLeft' q s))
      , Label "2" :<=>: prpInv2Type (Inv2 (sdlFromDualLeft' q s) (sdlToDualRight' q s))
      ]













{-  
  sdlToDual     :: Struct s x -> x -> o x
  sdlFromBidual :: Struct s x -> o (o x) -> x

instance TransformableOp s => SReflexive s Op where
  sdlToDual _     = Op
  sdlFromBidual _ = fromOp . fromOp

--------------------------------------------------------------------------------
-- sdlFromBidual' -

-- | prefixing a proxy.
sdlFromBidual' :: SReflexive s o => q o -> Struct s x -> o (o x) -> x
sdlFromBidual' _ = sdlFromBidual

--------------------------------------------------------------------------------
-- sdlToBidual -

-- | the induced mapping to the bi-dual objext, i.e. @'sdlToDual' ('tau1' s) '.' 'sdlToDual' s@.
sdlToBidual :: SReflexive s o => Struct s x -> x -> o (o x)
sdlToBidual s = sdlToDual (tau1 s) . sdlToDual s

-- | prefixing a proxy.
sdlToBidual' :: SReflexive s o => q o -> Struct s x -> x -> o (o x)
sdlToBidual' _ = sdlToBidual

--------------------------------------------------------------------------------
-- sdlRefl -

-- | the induced reflection, i.e. @'Inv2' ('sdlToBidual' s) ('sdlFromBidual' s)@.
sdlRefl :: SReflexive s o => Struct s x -> Inv2 (->) x (o (o x))
sdlRefl s = Inv2 (sdlToBidual s) (sdlFromBidual s)

sdlRefl' :: SReflexive s o => q o -> Struct s x -> Inv2 (->) x (o (o x))
sdlRefl' _ = sdlRefl

--------------------------------------------------------------------------------
-- prpSReflixive -

-- | validity according to 'SReflexive'.
prpSReflexive :: SReflexive s o
  => (Show x, Eq x, XStandard x)
  => (Show (o (o x)), Eq (o (o x)), XStandard (o (o x)))
  => (Eq (o x))
  => q o -> Struct s x -> Statement
prpSReflexive q s = Prp "SReflexive" :<=>:
  And [ Label "1" :<=>: (sdlToDual' q s' . sdlToDual' q s . sdlFromBidual' q s .=. id)
      , Label "2" :<=>: (sdlFromBidual' q s . sdlToDual' q s' . sdlToDual' q s .=. id)
      , Label "3" :<=>:
          (sdlToDual' q s . sdlFromBidual' q s .=. sdlFromBidual' q s' . sdlToDual' q s'')
      ]
  where s'  = tau1 s
        s'' = tau1 s'

--------------------------------------------------------------------------------
-- SDualisable -

-- | duality of structured types, based on a reflection.
--
-- __Property__ Let @'SDualisable' __s o__@, then for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy of @__q o__@, @s' = 'tau1' s@, @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'sdlRefl' q s@ and @'Inv2' _ v' = 'sdlRelf'' q s'@ in
--
-- (1) @'sdlToDual'' q s' '.' 'sdlToDual'' q s '.=.' u@.
--
-- (2) @'sdlFromDual'' q s '.=.' v '.' 'sdlToDual'' q s'@.
--
-- (3) @sdlToDual' q s . v .=. v' . sdlToDual' q s''@.
--
-- __Implications__
--
-- (i1) @'sdlFromDual'' q s '.' 'sdlToDual'' q s '.=.' id@.
--
-- (i2) @'sdlToDual'' q s . 'sdlFromDual'' q s '.=.' 'id'@.
--
-- __Note__
--
-- (1) From the properties 1 and 2 follows the property i1.
--
-- (2) Form the properties 1 and 3 follows the property i2.
class SReflexive s o => SDualisable s o where
  sdlFromDual :: Struct s x -> o x -> x
  sdlFromDual s = v . sdlToDual (tau1 s) where Inv2 _ v = sdlRefl s

instance TransformableOp s => SDualisable s Op where
  sdlFromDual _ = fromOp
  
{-
ff :: SDualisable s o => q o -> Struct s x -> o x -> o x
-- ff q s = sdlToDual' q s . sdlFromDual' q s
-- ff q s = sdlToDual' q s . v . sdlToDual' q s'
-- ff q s = v' . sdlToDual' q s'' . sdlToDual' q s'
ff q s = v' . u'
  where s'        = tau1 s
        -- s''       = tau1 s'
        Inv2 _ v  = sdlRefl' q s
        Inv2 u' v' = sdlRefl' q s'

f1 :: SDualisable s o => q o -> Struct s x -> o x -> x
f1 q s = v . sdlToDual' q s'
  where s'       = tau1 s
        Inv2 _ v = sdlRefl s

f2 :: SDualisable s o => q o -> Struct s x -> o (o x) -> o x
f2 q s = sdlToDual' q s . v
  where Inv2 _ v = sdlRefl s

f3 :: SDualisable s o => q o -> Struct s x -> o (o x) -> o x
f3 q s = v' . sdlToDual' q s''
  where s'        = tau1 s
        s''       = tau1 s'
        Inv2 _ v' = sdlRefl s'
-}

--------------------------------------------------------------------------------
-- sdlFromDual' -

sdlFromDual' :: SDualisable s o => q o ->  Struct s x -> o x -> x
sdlFromDual' _ = sdlFromDual

--------------------------------------------------------------------------------
-- prpSDualisable -

-- | validity accoriding to 'SDualisable'.
prpSDualisable :: SDualisable s o
  => (Show x, Eq x, XStandard x)
  => (Show (o x), Eq (o x), XStandard (o x))
  => (Show (o (o x)), Eq (o (o x)), XStandard (o (o x)))
  => q o
  -> Struct s x -> Statement
prpSDualisable q s = Prp "SDualisable" :<=>:
  And [ Label "1" :<=>: (sdlToDual' q s' . sdlToDual' q s .=. u)
      , Label "2" :<=>: (sdlFromDual' q s .=. v . sdlToDual' q s')
      , Label "3" :<=>: (sdlToDual' q s . v .=. v' . sdlToDual' q s'')
      -- , Label "3" :<=>: (sdlToDual' q s .=. sdlFromDual' q s' . u)
      ]
  && ( Label "Implications" :<=>:
  And [ Label "i1" :<=>: (sdlFromDual' q s . sdlToDual' q s .=. id)
      , Label "i2" :<=>: (sdlToDual' q s . sdlFromDual' q s .=. id)
      ]
     )
  where s'        = tau1 s
        s''       = tau1 s'
        Inv2 u v  = sdlRefl' q s
        Inv2 _ v' = sdlRefl' q s'
-}        
  
{-
--------------------------------------------------------------------------------
-- SDualisable1 -

-- | duality of 1-parameterized types over structured type.
--
-- __Properties__ Let @'SDualisable' __s o a b__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
-- holds: Let @q@ be any proxy of @__q o a b__@ in
--
-- (1) @'sdlFromDualRight'' q s '.' 'sdlToDualLeft'' q s '.=.' 'id'@.
--
-- (2) @'sdlFromDualLeft'' q s '.' 'sdlToDualRight'' q s '.=.' 'id'@.
class SDualisable1 s o a b where
  -- | mapping to the dual of @__a__@.
  sdlToDualLeft :: Struct s x -> a x -> b (o x)

  -- | mapping from the dual of @__b__@.
  sdlFromDualRight :: Struct s x -> b (o x) -> a x

  -- | mapping to the dual of @__b__@.
  sdlToDualRight :: Struct s x -> b x -> a (o x)

  -- | mapping from the dual of @__a__@.
  sdlFromDualLeft :: Struct s x -> a (o x) -> b x

--------------------------------------------------------------------------------
-- sdlToDualLeft' -

sdlToDualLeft' :: SDualisable1 s o a b => q o a b -> Struct s x -> a x -> b (o x)
sdlToDualLeft' _ = sdlToDualLeft

--------------------------------------------------------------------------------
-- sdlFromDualRigth' -

sdlFromDualRight' :: SDualisable1 s o a b => q o a b -> Struct s x -> b (o x) -> a x
sdlFromDualRight' _ = sdlFromDualRight

--------------------------------------------------------------------------------
-- sdlToDualRigth' -

sdlToDualRight' :: SDualisable1 s o a b => q o a b -> Struct s x -> b x -> a (o x)
sdlToDualRight' _ = sdlToDualRight

--------------------------------------------------------------------------------
-- sdlFromDualLeft'

sdlFromDualLeft' :: SDualisable1 s o a b => q o a b -> Struct s x -> a (o x) -> b x
sdlFromDualLeft' _ = sdlFromDualLeft

--------------------------------------------------------------------------------
-- prpSDualisable1 -

prpSDualisable1 :: SDualisable1 s o a b
  => (Show (a x), Eq (a x), XStandard (a x))
  => (Show (b x), Eq (b x), XStandard (b x))
  => q o a b -> Struct s x -> Statement
prpSDualisable1 q s = Prp "SDualisable1" :<=>:
  And [ Label "1" :<=>: (sdlFromDualRight' q s . sdlToDualLeft' q s .=. id)
      , Label "2" :<=>: (sdlFromDualLeft' q s . sdlToDualRight' q s .=. id)
      ]

--------------------------------------------------------------------------------
-- MapO - Applicative -

instance (Morphism h, Applicative h, SDualisable s o) => Applicative (MapO s o h) where
  amap (MapO h)   = amap h
  amap t@ToDual   = sdlToDual (domain t)
  amap f@FromDual = sdlFromDual (range f)

----------------------------------------
-- MapO - Applicative1 -

instance (Morphism h, Applicative1 h (Either1 a b), SDualisable1 s o a b)
  => Applicative1 (MapO s o h) (Either1 a b) where
  amap1 (MapO h)   = amap1 h
  amap1 t@ToDual   = \ab -> case ab of
    Left1 a  -> Right1 $ sdlToDualLeft (domain t) a
    Right1 b -> Left1 $ sdlToDualRight (domain t) b
  amap1 f@FromDual = \ab -> case ab of
    Left1 a  -> Right1 $ sdlFromDualLeft (range f) a
    Right1 b -> Left1 $ sdlFromDualRight (range f) b

-}


{-
--------------------------------------------------------------------------------
-- SReflexive -


-- | category having for each @__s__@-structured @__x__@ an isomorphism
-- @__i__ __x__ (__o__ (__o__ x))@.
--
-- __Note__ The parameter @q i o@ serves only as a proxy for @__i__@ and @__o__@.
class Category i => SReflexive s i o where
  sdlRefl :: q i o -> Struct s x -> Inv2 i x (o (o x))

instance SReflexive s (->) Op where
  sdlRefl _ _ = Inv2 (Op . Op) (fromOp . fromOp)
  
--------------------------------------------------------------------------------
-- SDualisable -

-- | duality for types with an underlying structure. 
--
-- __Property__  For all @q@ in @__q__ __i__ __o__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDualisable' __s__ __i__ __o__@ holds: Let @s' = 'sldTau' q s@, @s'' = 'sdlTau' q s'@,
-- @'Inv2' u v = sdlRefl q s@, @'Inv2' u' _ = 'sdlRefl' q s'@ and @(.=.) = 'eq2'@ in 
--
-- (1) @'sdlFromDual' q s '.' 'sdlToDual' q s .=. 'cOne' s@.
--
-- (2) @'sdlToDual' q s' '.' 'sdlToDual' q s .=, u@.
--
-- (3) @'sdlToDual' q s'' '.' u .=. u' '.' 'sdlToDual' q s@.
--
-- (4) @'sdlFromDual' q s '.' 'sdlFromDual' q ('sdlTau' q s) .=. v@.
--
-- __Note__
--
-- (1) The relation @'SDualisable' __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDual' q s '.' 'sdlFromDual' q s .=. 'cOne' s'@ may not hold in general!
--
-- (2) A sufficient condition for the properties 1 and 4 above is: The properties 2 and 3 hold and
-- @'sdlFromDual' q s = v '.' 'sdlToDual' q s'@, where
-- @'Inv2' _ r' = sdlRefl1 d s@. Hence it is sufficient to implement 'sdlToDual' 
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDual' 
-- as provided.
--
-- (3) The first parameter of type @__q i o__@ serves only as a proxy for @__i__@ and @__o__@.
class (SReflexive s i o, Transformable1 o s, Transformable s (ObjectClass i)) => SDualisable s i o where
  {-# MINIMAL (sdlToDual | sdlFromDual) #-}
  sdlToDual :: q i o -> Struct s x -> i x (o x)
  sdlToDual q s = sdlFromDual q (sdlTau q s) . u where Inv2 u _ = sdlRefl q s
  
  sdlFromDual :: q i o -> Struct s x -> i (o x) x
  sdlFromDual q s = v . sdlToDual q (sdlTau q s) where Inv2 _ v = sdlRefl q s

instance Transformable1 Op s => SDualisable s (->) Op where
  sdlToDual _ _   = Op
  sdlFromDual _ _ = fromOp
  
--------------------------------------------------------------------------------
-- sdlTau -

-- | transformation to the dual structure.
sdlTau :: SDualisable s i o => q i o -> Struct s x -> Struct s (o x)
sdlTau _ = tau1

--------------------------------------------------------------------------------
-- prpSDualisable -

-- | validity according to 'SDualisable'.
prpSDualisable :: SDualisable s i o
  => (forall x y . i x y -> i x y -> Statement)
  -> q i o -> Struct s x -> Statement
prpSDualisable (.=.) q s = Prp "SDualisable" :<=>:
  And [ Label "3" :<=>: ((sdlToDual q s'' . u) .=. (u' . sdlToDual q s))
      , Label "2" :<=>: ((sdlToDual q s' . sdlToDual q s) .=. u)
      , Label "1" :<=>: ((sdlFromDual q s . sdlToDual q s) .=. (cOne (tau s)))
      , Label "4" :<=>: ((sdlFromDual q s . sdlFromDual q s') .=. v)
      ]
  where s'         = sdlTau q s
        s''        = sdlTau q s'
        Inv2 u v   = sdlRefl q s
        Inv2 u' _ = sdlRefl q s'

prpSDualisableEq2 :: (SDualisable s i o, Eq2 i)
  => q i o -> Struct s x -> Statement
prpSDualisableEq2 = prpSDualisable (.=.) where f .=. g = Label "eq2" :<=>: eq2 f g :?> Params []

--------------------------------------------------------------------------------
-- SDualisableType -

-- | helper-class to circumvent undecidable instances.
class SDualisable s (->) o => SDualisableType s o

instance TransformableOp s => SDualisableType s Op

{-
--------------------------------------------------------------------------------
-- SDualisable1 -

-- | duality for parameterized types over types with an underlying structure.
--
-- __Property__ For all @d@ in @__d__ __i__ __o__ __a__ __b__@ and @s@ in @'Struct' __s__ __x__@ with
-- @'SDualisable1' __d__ __s__ __i__ __o__@, then holds:
--
-- (1) @'sdlFromDualRight' d s '.' 'sdlToDualLeft' d s = 'id'@.
--
-- (2) @'sdlToDualRight d ('sdlTau1' s) '.' 'sdlToDualLeft' d s = 'amap1Fst' d r@
-- where @'Inv2' r _ = 'sdlRefl1' d s@.
--
-- (3) @'sdlToDualRight' d s'' '.' 'amap1Snd' d r = 'amap1Fst' d r'' '.' 'sdlToDualRight' d s@ where
-- @s'' = 'sdlTau1' d s'@, @s' = 'sdlTau1' d s@, @'Inv2' r _ = 'sdlRefl1' d s@ and
-- @'Inv2' r'' _ = 'sdlRefl1' d s'@.
--
-- (4) @'sdlFromDualRight' d s '.' 'sdlFromDualLeft' d ('sdlTau1' s) = 'amap1Fst' d r'@
-- where @'Inv2' _ r' = 'sdlRefl1' d s@.
--
-- __Note__
--
-- (1) The relation @'SDualisable1' __d__ __s__ __i__ __o__@ is not necessarily /symmetric/,
-- i.e. @'sdlToDualLeft' d s' '.' 'sdlFromDualRight' d s' = 'id'@ dose not hold in general!
--
-- (2) A sufficient condition for the properties 1 and 4 above is: The properties 2 and 3 hold and
-- @'sdlFromDualRight' d s = 'amap1Fst' d r' '.' 'sdlToDualRight' d s'@ and
-- @'amap1Snd' d r' '.' 'sdlToDualLeft' d s'@ where @s' = 'sdlTau1' d s@ and
-- @Inv2 _ r' = sdlRefl1 d s@´. Hence it is sufficient to implement 'sdlToDualLeft' and 'sdlToDualRight'
-- such that the properties 2 and 3 hold and leaving the implementation of 'sdlFromDualRight' and
-- 'sdlFromFualSnd' as provided.
class (SReflexive s i o, BiFunctorial1 i (d i o), Transformable1 o s) => SDualisable1 d s i o where
  {-# MINIMAL (sdlToDualLeft, sdlToDualRight | sdlFromDualRight, sdlFromDualLeft) #-}
  
  -- | mapping to the dual of @__a__ __x__@.
  sdlToDualLeft :: d i o a b -> Struct s x -> a x -> b (o x)
  sdlToDualLeft d s = sdlFromDualLeft d (sdlTau1 d s) . amap1Fst d r where Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__a__ __x__@.
  sdlFromDualRight :: d i o a b -> Struct s x -> b (o x) -> a x
  sdlFromDualRight d s = amap1Fst d r' . sdlToDualRight d (sdlTau1 d s) where Inv2 _ r' = sdlRefl1 d s

  -- | mapping to the dual of @__b__ __x__@.
  sdlToDualRight :: d i o a b -> Struct s x -> b x -> a (o x)
  sdlToDualRight d s = sdlFromDualRight d (sdlTau1 d s) . amap1Snd d r where  Inv2 r _ = sdlRefl1 d s

  -- | mapping from the dual of @__b__ __x__@.
  sdlFromDualLeft :: d i o a b -> Struct s x -> a (o x) -> b x
  sdlFromDualLeft d s = amap1Snd d r' . sdlToDualLeft d (sdlTau1 d s) where Inv2 _ r' = sdlRefl1 d s

--------------------------------------------------------------------------------
-- sdlRefl1 -

-- | the associated reflection.
sdlRefl1 :: SDualisable1 d s i o => d i o a b -> Struct s x -> Inv2 i x (o (o x))
sdlRefl1 d = sdlRefl (q d) where
  q :: forall k d (i :: k) o a b .  d i o a b -> Proxy2 i o
  q _ = Proxy2

--------------------------------------------------------------------------------
-- sdlFncFst -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the first parameter @__a__@.
sdlFncFst :: SDualisable1 d s i o => d i o a b -> Struct s x -> Functor1 i a
sdlFncFst d _ = fnc1Fst d

--------------------------------------------------------------------------------
-- sdlFncSnd -

-- | attest of being 'Functorial1' according to the category @__i__@
-- and the second parameter @__b__@.
sdlFncSnd :: SDualisable1 d s i o => d i o a b -> Struct s x -> Functor1 i b
sdlFncSnd d _ = fnc1Snd d

--------------------------------------------------------------------------------
-- sdlTau1 -

-- | promoting a structure to its opposite structure.
sdlTau1 :: SDualisable1 d s i o => d i o a b -> Struct s x -> Struct s (o x)
sdlTau1 _ = tau1

--------------------------------------------------------------------------------
-- prpSDualisable1 -

-- | validity accorting to 'SDualisable1'.
prpSDualisable1 :: SDualisable1 d s i o
  => (Eq (a x), Show (a x), Eq (a (o (o x))), Show (a (o (o x))))
  => (Eq (a (o (o (o x)))), Show (b x))
  =>  d i o a b -> Struct s x -> X (a x) -> X (b x) -> X (a (o (o x))) -> Statement
prpSDualisable1 d s xa xb xa'' = Prp "SDualisable1" :<=>:
  And [ Label "3" :<=>: Forall xb
        (\b -> let s'  = sdlTau1 d s
                   s'' = sdlTau1 d s' 
                   Inv2 r _  =  sdlRefl1 d s
                   Inv2 r'' _ = sdlRefl1 d s'
                in ((sdlToDualRight d s'' $ amap1Snd d r b) == (amap1Fst d r'' $ sdlToDualRight d s b))
                     :?> Params ["b x":=show b]
        )
      , Label "2" :<=>: Forall xa
        (\a -> ((sdlToDualRight d (sdlTau1 d s) $ sdlToDualLeft d s a) == amap1Fst d r a)
                  :?> Params ["a x":=show a]
        )
      , Label "1" :<=>: Forall xa
        (\a -> ((sdlFromDualRight d s $ sdlToDualLeft d s a) == a) :?> Params ["a x":=show a]   
        )
      , Label "4" :<=>: Forall xa''
        (\a'' -> ((sdlFromDualRight d s $ sdlFromDualLeft d (sdlTau1 d s) a'') == amap1Fst d r' a'')
                   :?> Params ["a (o (o x))":=show a'']
        )
      ]
  where Inv2 r r' = sdlRefl1 d s
-}

--------------------------------------------------------------------------------
-- Duality -

newtype Duality d a x = Duality (Either1 a (d a) x)

--------------------------------------------------------------------------------
-- SDualisable1 -

-- | duality for 1-parameterized types over structured types.
--
-- __Property__ Let @'SDualisable' __s o d a__@, then for all @q@ in @__q__ __o__@, @__x__@  and
--  @s@ in @'Struct' __s__ __x__@ holds:
--
-- (1) @'sdlFromDual1' q s '.' 'sdlToDual1' q s '.=.' 'id@.
--
-- (2) For all @a@ in @__a__ __x__@ holds: @'sdlToDual1' q s ('Duality' ('Left1' a))@ matches
-- @'Duality1' ('Right1' a')@.
class SDualisable1 s o d a where
  sdlToDual1 :: q o -> Struct s x -> Duality d a x -> Duality d a (o x)
  sdlFromDual1 :: q o -> Struct s x -> Duality d a (o x) -> Duality d a x 
  
--------------------------------------------------------------------------------
-- MapO -

data MapO s o h x y where
  MapO     :: Transformable (ObjectClass h) s => h x y -> MapO s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => MapO s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => MapO s o h (o x) x

instance Transformable s Typ => TransformableObjectClassTyp (MapO s o h)

--------------------------------------------------------------------------------
-- MapO - Entity2 -

instance Show2 h => Show2 (MapO s o h) where
  show2 (MapO h)  = "MapO (" ++ show2 h ++ ")"
  show2 ToDual    = "ToDual"
  show2 FromDual  = "FromDual"

instance Eq2 h => Eq2 (MapO s o h) where
  eq2 (MapO f) (MapO g) = eq2 f g
  eq2 ToDual ToDual     = True
  eq2 FromDual FromDual = True
  eq2 _ _               = False

instance Validable2 h => Validable2 (MapO s o h) where
  valid2 (MapO h) = valid2 h
  valid2 _          = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (MapO s o h)

--------------------------------------------------------------------------------
-- MapO - Morphism -

instance Morphism h => Morphism (MapO s o h) where
  type ObjectClass (MapO s o h) = s

  homomorphous (MapO h) = tauHom (homomorphous h)
  homomorphous ToDual    = Struct :>: Struct
  homomorphous FromDual  = Struct :>: Struct

--------------------------------------------------------------------------------
-- MapO - Applicative -

oMorType :: MapO s o h x y -> Proxy2 (->) o
oMorType _ = Proxy2

instance (Morphism h, Applicative h, SDualisableType s o) => Applicative (MapO s o h) where
  amap (MapO h)   = amap h
  amap t@ToDual   = sdlToDual (oMorType t) (domain t)
  amap f@FromDual = sdlFromDual (oMorType f) (range f)

----------------------------------------
-- MapO - Applicative1 -

oMorO :: MapO s o h x y -> Proxy o
oMorO _ = Proxy

instance (Morphism h, Applicative1 h (Duality d a), SDualisable1 s o d a)
  => Applicative1 (MapO s o h) (Duality d a) where
  amap1 (MapO h)   = amap1 h
  amap1 t@ToDual   = sdlToDual1 (oMorO t) (domain t)
  amap1 f@FromDual = sdlFromDual1 (oMorO f) (range f) 


--------------------------------------------------------------------------------
-- PathMapO -

type PathMapO s o h = Path (MapO s o h)

--------------------------------------------------------------------------------
-- OCat -

newtype OCat s o h x y = OCat (PathMapO s o h x y)
  deriving (Show2,Validable2)

deriving instance (Morphism h, Eq2 h, Transformable s Typ) => Eq2 (OCat s o h)

instance (Entity2 h, Morphism h, Transformable s Typ, Typeable s, Typeable o) => Entity2 (OCat s o h)

-}





