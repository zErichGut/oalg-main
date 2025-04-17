
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneKindSignatures
  , DataKinds
#-}

-- |
-- Module      : OAlg.Hom.SDuality
-- Description : duality of structured data.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Duality of structured data.
module OAlg.Hom.SDuality
  (

{-
    -- * Dualisable
    SDualisable(..), sdlToDual', sdlFromDual'
  , SReflexive(..), sdlCo', sdlRefl'

    -- * Dualisable 1
  , SDualisable1(..)
  , sdlToDualLeft', sdlFromDualLeft'  
  , sdlToDualRight', sdlFromDualRight'

  
  , SReflexive1(..) --, sdlRefl1
  , sdlFromDualLeft, sdlFromDualRight

  , sdlCoLeft', sdlCoRight'
  , sdlReflLeft', sdlReflRight'

    -- * Proposition
  , prpSDualisable, prpSReflexive
  , prpReflexive1
-}
  
  ) where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDual

import OAlg.Data.Singleton
import OAlg.Data.Constructable
import OAlg.Data.Variant

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
class (Category c, Transformable1 o s) => SReflexive c s o d where
  sdlToDual :: Struct s x -> c (d x) (d (o x))
  sdlRefl :: Struct s x -> Inv2 c (d x) (d (o (o x)))

sdlFromDual :: SReflexive c s o d => Struct s x -> c (d (o x)) (d x)
sdlFromDual s = v . sdlToDual (tau1 s) where Inv2 _ v = sdlRefl s

instance (Morphism h, ApplicativeG d h c, SReflexive c s o d)
  => ApplicativeG d (MapSDual s o h) c where
  amapG (MapSDual h) = amapG h
  amapG t@ToDual   = sdlToDual (domain t)
  amapG f@FromDual = sdlFromDual (range f)

class TransformableGObjectClass d (MapSDual s o h) c => TransformableGMapSDual d s o h c

instance ( Morphism h, ApplicativeG d h c, SReflexive c s o d
         , TransformableGMapSDual d s o h c
         )
  => ApplicativeG d (CatSDual s o h) c where
  amapG = amapG . form


-- instance TransformableGMapSDual d s o h c => TransformableGObjectClass d (CatSDual s o h) c

instance ( Morphism h, ApplicativeG d h c, SReflexive c s o d
         -- {-, TransformableGMapSDual d s o h c
         ) => FunctorialG d (CatSDual s o h) c


{-

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
-- sdlReflection -

sdlReflection :: SReflexive r s o => f s x -> g r y -> r o
sdlReflection _ _ = unit

--------------------------------------------------------------------------------
-- sdlToDual' -

sdlToDual' :: SReflexive r s o => Struct s x -> SDual r x -> SDual r (o x)
sdlToDual' s d@(SDual x) = SDual (sdlCo r s x) where r = sdlReflection s d

--------------------------------------------------------------------------------
-- sdlFromDual' -

sdlFromDual' :: SReflexive r s o => Struct s x -> SDual r (o x) -> SDual r x
sdlFromDual' s x' = SDual (v x'') where
  r         = sdlReflection s x'
  SDual x'' = sdlToDual' (tau1 s) x'
  Inv2 _ v  = sdlRefl r s
  
--------------------------------------------------------------------------------
-- SReflection -

data SReflection (o :: Type -> Type) = SReflection

instance Singleton (SReflection o) where unit = SReflection

instance Transformable1 Op s => SReflexive SReflection s Op where
  sdlCo _ _   = Op
  sdlRefl _ _ = Inv2 (Op . Op) (fromOp . fromOp)

--------------------------------------------------------------------------------
-- SDual -

type SDual :: ((Type -> Type) -> Type) -> Type -> Type
newtype SDual r x = SDual x

instance (Morphism h, Applicative h, SReflexive r s o) => Applicative1 (MapSDual s o h) (SDual r) where
  amap1 (MapSDual h) = \(SDual x) -> SDual $ amap h x
  amap1 t@ToDual     = sdlToDual' (domain t)
  amap1 f@FromDual   = sdlFromDual' (range f)

instance (Morphism h, Applicative h, SReflexive r s o) => Applicative1 (CatSDual s o h) (SDual r) where
  amap1 = amap1 . form
  
instance (Morphism h, Applicative h, SReflexive r s o) => Functorial1 (CatSDual s o h) (SDual r)

--------------------------------------------------------------------------------
-- sdlToDual -

sdlToDual :: (Transformable1 o s, Functorial1 (CatSDual s o h) d)
  => q h -> Struct s x -> d x -> d (o x)
sdlToDual q s = amap1 toDual where
  Contravariant2 toDual = sctToDual' q s
  
  sctToDual' :: Transformable1 o s
             => q h -> Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
  sctToDual' _ = sctToDual
-}







{-
data SDual r s o x where
  SDual :: SReflexive r s o => SDual r s o x
-}  
-- class (SReflexive r s o,  => MapSDualReflexive r s o

-- instance SReflexive r s o => Applicative (MapSDual s o h) where
  
{-
class SReflexive r s o => ApplicativeSReflexive r s o

instance SReflexive r s o => ApplicativeMapSDual s o h
-}

{-
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
  => Structure ExtEq x
  => Structure ExtEq (o x)
  => Structure ExtEq (o (o x))
  => q o -> Struct s x -> Statement
prpSReflexive q s = Prp "SReflexive" :<=>:
  And [ Label "sdlRefl" :<=>: valid (Inv2 (ExtEqual u) (ExtEqual v))
      , Label "1" :<=>: (ExtEqual (sdlCo' q s' . sdlCo' q s) .=. ExtEqual u)
      , Label "2" :<=>: (ExtEqual (sdlCo' q s . v) .=. ExtEqual (v' . sdlCo' q s''))
      ]
  where s'        = tau1 s
        s''       = tau1 s'
        Inv2 u v  = sdlRefl' q s
        Inv2 _ v' = sdlRefl' q s'

--------------------------------------------------------------------------------
-- SDualisable -

-- | dualisable @__s__@-structured types.
--
-- __Property__ Let @'SDualisable' __s o__@, then for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy of @__q o__@ in
--
-- (1) @'Inv2' ('sdlFromDual'' q s) ('sdlToDual'' q s)@ is 'valid'.
--
-- __Note__
--
-- (1) If a implementation of 'SDualisable' is given by the default implemetation via 'SReflexive'
-- then holds: The property 1 above follows from the property 1 and 2 of 'SReflextion' and the
-- validity of 'sdlRefl'.
--
-- (2) This class is mearly used to implemnent the 'Applicative' property for 'SDualityCat'.
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
  => Structure ExtEq x
  => Structure ExtEq (o x)
  => q o
  -> Struct s x -> Statement
prpSDualisable q s = Prp "SDualisable" :<=>:
  Label "1" :<=>: valid (Inv2 (ExtEqual (sdlFromDual' q s)) (ExtEqual (sdlToDual' q s)))

--------------------------------------------------------------------------------
-- SReflexive1 -

-- | duality of 1-parameterized types over @__s__@-structured types given by reflections.
--
-- __Property__ Let @'SReflexive' __s o a b__@, then for all @__x__@ and
-- @s@ in @'Struct' __s x__@ holds:
-- Let @q@ be any proxy in @__q o__@, @s' = 'tau1' s@ and @s'' = 'tau1' s'@,
-- @'Inv2' uLeft vLeft = 'sdlReflLeft'' q s@, @'Inv2' _ vLeft' = 'sdlReflLeft'' q s'@,
-- @'Inv2' uRight vRight = 'sdlReflRight'' q s@ and @'Inv2' _ vRight' = 'sdlReflRight'' q s'@ in
--
-- @'Inv2' u v = 'sdlRelf'' q s@ and @'Inv2' _ v' = 'sdlRefl'' q s'@ in
--
-- (1) @'sdlCoRight'' q s' '.' 'sdlCoLeft'' q s '.=.' uLeft@.
--
-- (2) @'sdlCoLeft'' q s' '.' sdlCoRight' q s '.=.' uRight@.
--
-- (3) @'sdlCoLeft'' q s '.' vLeft '.=.' vRight' '.' sdlCoLeft' q s''@.
--
-- (4) @'sdlCoRight'' q s '.' vRight '.=.' vLeft' '.' sdlCoRight' q s''@.
class (Singleton (r o a b), Transformable1 o s) => SReflexive1 r s o a b where
  
  sdlToDualLeft :: r o a b -> Struct s x -> a x -> b (o x)
  sdlToDualRight :: r o a b -> Struct s x -> b x -> a (o x)
  sdlReflLeft :: r o a b -> Struct s x -> Inv2 (->) (a x) (a (o (o x)))
  sdlReflRight :: r o a b -> Struct s x -> Inv2 (->) (b x) (b (o (o x)))

--------------------------------------------------------------------------------
-- sdlRefl1 -

sdlRefl1 :: SReflexive1 r s o a b => q s -> r o a b
sdlRefl1 _ = unit

--------------------------------------------------------------------------------
-- sdlFromDualRight -

sdlFromDualRight :: SReflexive1 r s o a b => r o a b -> Struct s x -> b (o x) -> a x
sdlFromDualRight r s = v . sdlToDualRight r (tau1 s) where Inv2 _ v = sdlReflLeft r s

--------------------------------------------------------------------------------
-- sdlFromDualLeft -

sdlFromDualLeft :: SReflexive1 r s o a b => r o a b -> Struct s x -> a (o x) -> b x
sdlFromDualLeft r s = v . sdlToDualLeft r (tau1 s) where Inv2 _ v = sdlReflRight r s

{-
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
  => Structure ExtEq (a x)
  => Structure ExtEq (a (o x))
  => Structure ExtEq (a (o (o x)))
  => Structure ExtEq (b x)
  => Structure ExtEq (b (o x))
  => Structure ExtEq (b (o (o x)))
  => q o a b -> Struct s x -> Statement
prpReflexive1 q s = Prp "Reflexive1" :<=>:
  And [ Label "1" :<=>: (ExtEqual (sdlCoRight' q s' . sdlCoLeft' q s) .=. ExtEqual uLeft)
      , Label "2" :<=>: (ExtEqual (sdlCoLeft' q s' . sdlCoRight' q s) .=. ExtEqual uRight)
      , Label "3" :<=>: (ExtEqual (sdlCoLeft' q s . vLeft) .=. ExtEqual (vRight' . sdlCoLeft' q s''))
      , Label "4" :<=>: (ExtEqual (sdlCoRight' q s . vRight) .=. ExtEqual (vLeft' . sdlCoRight' q s''))
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
  And [ Label "1" :<=>: valid (Inv2 (ExtEqual (sdlFromDualRight' q s)) (ExtEqual (sdlToDualLeft' q s)))
      , Label "2" :<=>: valid (Inv2 (ExtEqual (sdlFromDualLeft' q s)) (ExtEqual (sdlToDualRight' q s)))
      ]


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- first steps of generlaizing reflections

class AA a b f where
  aa :: a x y -> b (f x) (f y)

aa' :: AA a b f => q b f -> a x y -> b (f x) (f y)
aa' _ = aa

ff :: AA (->) (->) f => (x -> y) -> f x -> f y
ff = aa

gg :: AA a (->) f => a x y -> f x -> f y
gg = aa

newtype I x = I x

hh :: AA a (->) I => a x y -> x -> y
hh a x = y where I y = aa a (I x)

-- | functorial form @__a__@ to @__b__@ according to the type map @__f__@.
class (Category a, Category b, AA a b f) => FF a b f

-- | structural transformation
class TT a b f where
  tt :: Struct a x -> Struct b (f x)

prpFFCmp :: (FF a b f, Eq2 b) => q b f -> a y z -> a x y -> Statement
prpFFCmp q f g = eq2 (aa' q (f . g)) (aa' q f . aa' q g) :?> Params []

prpFFId :: (FF a b f, TT (ObjectClass a) (ObjectClass b) f, Eq2 b)
  => q a b f -> Struct (ObjectClass a) x -> Statement
prpFFId q s = eq2 (aa (cOneDom q s)) (cOneRng q (tt s)) :?> Params [] 

cOneDom :: FF a b f => q a b f -> Struct (ObjectClass a) x -> a x x
cOneDom _ = cOne

cOneRng :: FF a b f => q a b f -> Struct (ObjectClass b) (f x) -> b (f x) (f x)
cOneRng _ = cOne

newtype SS a x = SS (Struct (ObjectClass a) x)

-- | natural transformation between the two functorials
class (FF a b f, FF a b g) => NN a b f g where
  nn :: SS a x -> b (f x) (g x)

prpNN :: (NN a b f g, Eq2 b) => q a b f g -> a x y -> Statement
prpNN q a = eq2 (nnRng q a . aa a) (aa a . nnDom q a) :?> Params []

nnDom :: NN a b f g => q a b f g -> a x y -> b (f x) (g x)
nnDom q a = nn (ssDom q a)

nnRng :: NN a b f g => q a b f g -> a x y -> b (f y) (g y)
nnRng q a = nn (ssRng q a)

ssDom :: NN a b f g => q a b f g -> a x y -> SS a x
ssDom _ a = SS (domain a)

ssRng :: NN a b f g => q a b f g -> a x y -> SS a y
ssRng _ a = SS (range a)

class (NN (->) (->) I o, Transformable1 o s) => SR s o

srCo :: SR s o => q s o -> Struct s x -> x -> o x
srCo _ s = nn (sType s) . I

sType :: Struct s x -> SS (->) x
sType _ = SS Struct
-}

-}
