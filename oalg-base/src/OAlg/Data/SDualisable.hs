
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
-- Description : duality for structured types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- duality for structured types.
module OAlg.Data.SDualisable
  (
    -- * Structural Duality
    -- ** Dualisable
    SDualisable, sdlToDual
  
  , SDualisableG
  , SReflexiveG(..)

    -- ** Bi-Dualisable
  , SBiDualisable
  , sdlToDualLft
  , SDual(..)

    -- * Category
  , SDualCat(), sctToDual, sctToDual'
    
    -- * Map
  , SDualMap(..)
  , PathSDualMap, rdcPathSDualMap
    
  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Identity
import OAlg.Data.Either
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant


--------------------------------------------------------------------------------
-- SDualMap -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data SDualMap o h x y where
  SDualMap :: h x y -> SDualMap o h x y
  ToDual   :: (Structure (ObjectClass h) x, Structure (ObjectClass h) (o x)) => SDualMap o h x (o x)
  FromDual :: (Structure (ObjectClass h) x, Structure (ObjectClass h) (o x)) =>  SDualMap o h (o x) x

instance TransformableGObjectClass d h c => TransformableGObjectClass d (SDualMap o h) c

--------------------------------------------------------------------------------
-- SDualMap - Disjunctive -

instance Disjunctive (SDualMap o h x y) where
  variant (SDualMap _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (SDualMap o h)

--------------------------------------------------------------------------------
-- SDualMap - Entity2 -

instance Show2 h => Show2 (SDualMap o h) where
  show2 (SDualMap h) = "SDualMap (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (SDualMap o h) where
  eq2 (SDualMap f) (SDualMap g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (SDualMap o h) where
  valid2 (SDualMap h) = valid2 h
  valid2 _            = SValid

instance (Entity2 h, Typeable o) => Entity2 (SDualMap o h)

--------------------------------------------------------------------------------
-- SDualMap - Morphism -

instance Morphism h => Morphism (SDualMap o h) where
  type ObjectClass (SDualMap o h) = ObjectClass h

  homomorphous (SDualMap h) = homomorphous h
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance TransformableObjectClassTyp h => TransformableObjectClassTyp (SDualMap o h)

--------------------------------------------------------------------------------
-- PathSDualMap -

-- | path of 'SDualMap'.
type PathSDualMap o h = Path (SDualMap o h)

--------------------------------------------------------------------------------
-- rdcPathSDualMap -

rdcPathSDualMap :: PathSDualMap o h x y -> Rdc (PathSDualMap o h x y)
rdcPathSDualMap p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathSDualMap
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathSDualMap
  p' :. p''                -> rdcPathSDualMap p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSDualMap o h x y) where
  reduce = reduceWith rdcPathSDualMap

--------------------------------------------------------------------------------
-- SDualCat -

-- | category for structural dualities.
newtype SDualCat o h x y = SDualCat (PathSDualMap o h x y)
  deriving (Show, Show2, Validable, Validable2)

deriving instance (Morphism h, TransformableObjectClassTyp h, Eq2 h) => Eq2 (SDualCat o h)

instance (Morphism h, Entity2 h, TransformableObjectClassTyp h, Typeable o)
  => Entity2 (SDualCat o h)

--------------------------------------------------------------------------------
-- SDualCat - Disjunctive -

instance Disjunctive2 (SDualCat o h)    where variant2 = restrict variant2
instance Disjunctive (SDualCat o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- SDualCat - Constructable -

instance Exposable (SDualCat o h x y) where
  type Form (SDualCat o h x y) = PathSDualMap o h x y
  form (SDualCat p) = p

instance Constructable (SDualCat o h x y) where make = SDualCat . reduce

--------------------------------------------------------------------------------
-- SDualCat - Category -

instance Morphism h => Morphism (SDualCat o h) where
  type ObjectClass (SDualCat o h) = ObjectClass h
  homomorphous (SDualCat p) = homomorphous p

instance Morphism h => Category (SDualCat o h) where
  cOne = make . IdPath
  SDualCat f . SDualCat g = make (f . g)

--------------------------------------------------------------------------------
-- sctToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'ToDual'
-- in'SDualCat'.
sctToDualStruct :: ObjectClass h ~ s
  => Struct s x -> Struct s (o x) -> Variant2 Contravariant (SDualCat o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

-- | 'ToDual' as a 'Contravaraint' morphism in 'SDualCat'.
sctToDual :: (ObjectClass h ~ s, Transformable1 o s)
  => Struct s x -> Variant2 Contravariant (SDualCat o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

-- | prefixing a proxy.
sctToDual' :: (ObjectClass h ~ s, Transformable1 o s)
  => q o h -> Struct s x -> Variant2 Contravariant (SDualCat o h) x (o x)
sctToDual' _ = sctToDual

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
-- SDuality -

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
-- SDualisableGMorphism -

-- | helper class to avoid undecidable instances.
class (Morphism h, SDualisableG c (ObjectClass h) o d) => SDualisableGMorphism c h o d

--------------------------------------------------------------------------------
-- SDualCat - FunctorialG -

instance (ApplicativeG d h c, SDualisableGMorphism c h o d)
  => ApplicativeG d (SDualMap o h) c where
  amapG (SDualMap h) = amapG h
  amapG t@ToDual     = toDualG (domain t)
  amapG f@FromDual   = fromDualG (range f)

instance ( ApplicativeG d h c, SDualisableGMorphism c h o d
         , TransformableGObjectClass d h c
         ) => ApplicativeG d (SDualCat o h) c where
  amapG = amapG . form

instance ( Category c, ApplicativeG d h c, SDualisableGMorphism c h o d
         , TransformableGObjectClass d h c
         ) => ApplicativeGMorphism d (SDualCat o h) c

instance ( Category c, ApplicativeG d h c, SDualisableGMorphism c h o d
         , TransformableGObjectClass d h c
         ) => FunctorialG d (SDualCat o h) c


--------------------------------------------------------------------------------
-- SDualisableG -

type SDualisable c s o h = (Transformable1 o s, ObjectClass h ~ s, FunctorialG Id (SDualCat o h) c)

--------------------------------------------------------------------------------
-- sdlToDual -

sdlToDual :: SDualisable (->) s o h => q o h -> Struct s x -> x -> o x
sdlToDual q s = fromIdG $ amapG toDual where Contravariant2 toDual = sctToDual' q s

-- sdlToDual :: SDualisableG (->) s o Id => q o -> Struct s x -> x -> o x
-- sdlToDual _ s x = x' where Id x' = toDualG s (Id x) 

--------------------------------------------------------------------------------
-- SBiDualisableG -

class (SReflexiveG c s o a, SReflexiveG c s o b, Transformable1 o s)
  => SBiDualisableG c s o a b where
  toDualLft :: Struct s x -> c (a x) (b (o x))
  toDualRgt :: Struct s x -> c (b x) (a (o x))

  fromDualLft :: Struct s x -> c (b (o x)) (a x)
  fromDualLft s = v . toDualRgt (tau1 s) where Inv2 _ v = reflG s
  
  fromDualRgt :: Struct s x -> c (a (o x)) (b x)
  fromDualRgt s = v . toDualLft (tau1 s) where Inv2 _ v = reflG s
--------------------------------------------------------------------------------
-- SDual -

newtype SDual a b x = SDual (Either1 a b x)

--------------------------------------------------------------------------------
-- fromSDual -

fromSDual :: SDual a b x -> Either1 a b x
fromSDual (SDual ab) = ab

--------------------------------------------------------------------------------
-- amapEither -

amapEither :: (ApplicativeG a h (->), ApplicativeG b h (->)) => h x y -> Either1 a b x -> Either1 a b y
amapEither h (Left1 a)  = Left1 (amapG h a)
amapEither h (Right1 b) = Right1 (amapG h b) 

--------------------------------------------------------------------------------
-- toDualEither -

toDualEither :: SBiDualisableG (->) s o a b => Struct s x -> Either1 a b x -> Either1 a b (o x)
toDualEither s (Left1 a)  = Right1 (toDualLft s a)
toDualEither s (Right1 b) = Left1 (toDualRgt s b)


--------------------------------------------------------------------------------
-- reflEitherTo -

reflEitherTo :: SBiDualisableG (->) s o a b
  => Struct s x -> (->) (Either1 a b x) (Either1 a b (o (o x)))
reflEitherTo s (Left1 a)  = Left1 (u a)  where Inv2 u _ = reflG s
reflEitherTo s (Right1 b) = Right1 (u b) where Inv2 u _ = reflG s 

--------------------------------------------------------------------------------
-- reflEitherFrom -

reflEitherFrom :: SBiDualisableG (->) s o a b
  => Struct s x -> (->) (Either1 a b (o (o x))) (Either1 a b x)
reflEitherFrom s (Left1 a'') = Left1 (v a'') where Inv2 _ v   = reflG s
reflEitherFrom s (Right1 b'') = Right1 (v b'') where Inv2 _ v = reflG s


------------------------------------------------------------------------------------------
-- SDual - SReflexive -

instance SBiDualisableG (->) s o a b => SReflexiveG (->) s o (SDual a b) where
  reflG s = Inv2 u v where
    u = SDual . reflEitherTo s . fromSDual
    v = SDual . reflEitherFrom s . fromSDual
    
instance SBiDualisableG (->) s o a b => SDualisableG (->) s o (SDual a b) where
  toDualG s = SDual . toDualEither s . fromSDual

--------------------------------------------------------------------------------
-- SBiDualisable -

class (Transformable1 o s, ObjectClass h ~ s, FunctorialG (SDual a b) (SDualCat o h) c)
  => SBiDualisable c s o h a b

class SDualisableGMorphism c h o (SDual a b) => SDualisableGMorphismSDual c h o a b

instance ( Transformable1 o s, ObjectClass h ~ s, ApplicativeG (SDual a b) h c
         , SDualisableGMorphismSDual c h o a b
         , TransformableGObjectClass (SDual a b) h c
         )
  => SBiDualisable c s o h a b

--------------------------------------------------------------------------------
-- implErrorSBidualisable -

-- | implementation error for 'SBiDualisable'
implErrorSBidualisable :: String -> AlgebraicException
implErrorSBidualisable f = ImplementationError ("SBiDualisable at: " ++ f)
                             
--------------------------------------------------------------------------------
-- sdlToDualLft -

sdlToDualLft :: SBiDualisable (->) s o h a b => q a b o h -> Struct s x -> a x -> b (o x)
sdlToDualLft q s a = case amapG toDual (SDual (Left1 a)) of
     SDual (Right1 b') -> b'
     _                 -> throw (implErrorSBidualisable "sdlToDualLft")
  where Contravariant2 toDual = sctToDual' q s


