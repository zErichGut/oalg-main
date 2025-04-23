
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
-- Module      : OAlg.Category.SDual
-- Description : functor to dualisable structured types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- functor to dualisable structured types.
module OAlg.Category.SDual
  (
    -- * Category
    SDualCat(), sctToDual, sctToDual'
    
    -- * Map
  , SDualMap(..)
  , PathSDualMap, rdcPathSDualMap

  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Either
import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant
import OAlg.Data.SDualisable


--------------------------------------------------------------------------------
-- SDualMap -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data SDualMap s o h x y where
  SDualMap :: h x y -> SDualMap s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => SDualMap s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) =>  SDualMap s o h (o x) x

--------------------------------------------------------------------------------
-- SDualMap - Disjunctive -

instance Disjunctive (SDualMap s o h x y) where
  variant (SDualMap _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (SDualMap s o h)

--------------------------------------------------------------------------------
-- SDualMap - Entity2 -

instance Show2 h => Show2 (SDualMap s o h) where
  show2 (SDualMap h) = "SDualMap (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (SDualMap s o h) where
  eq2 (SDualMap f) (SDualMap g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (SDualMap s o h) where
  valid2 (SDualMap h) = valid2 h
  valid2 _            = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (SDualMap s o h)

--------------------------------------------------------------------------------
-- SDualMap - Morphism -

instance (Morphism h, ObjectClass h ~ s) => Morphism (SDualMap s o h) where
  type ObjectClass (SDualMap s o h) = s

  homomorphous (SDualMap h) = homomorphous h
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance (TransformableGObjectClass d h c, ObjectClass h ~ s)
  => TransformableGObjectClass d (SDualMap s o h) c

instance Transformable s Typ => TransformableObjectClassTyp (SDualMap s o h)

--------------------------------------------------------------------------------
-- PathSDualMap -

-- | path of 'SDualMap'.
type PathSDualMap s o h = Path (SDualMap s o h)

--------------------------------------------------------------------------------
-- rdcPathSDualMap -

rdcPathSDualMap :: PathSDualMap s o h x y -> Rdc (PathSDualMap s o h x y)
rdcPathSDualMap p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathSDualMap
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathSDualMap
  p' :. p''                -> rdcPathSDualMap p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathSDualMap s o h x y) where
  reduce = reduceWith rdcPathSDualMap

--------------------------------------------------------------------------------
-- SDualCat -

-- | category for structural dualities.
newtype SDualCat s o h x y = SDualCat (PathSDualMap s o h x y)
  deriving (Show, Show2)

deriving instance (Morphism h, ObjectClass h ~ s, Validable2 h) => Validable2 (SDualCat s o h)
deriving instance (Morphism h, ObjectClass h ~ s, Validable2 h) => Validable (SDualCat s o h x y)
deriving instance (Morphism h, ObjectClass h ~ s, Transformable s Typ, Eq2 h) => Eq2 (SDualCat s o h)


instance (Morphism h, ObjectClass h ~ s, Entity2 h, Transformable s Typ, Typeable s, Typeable o)
  => Entity2 (SDualCat s o h)

--------------------------------------------------------------------------------
-- SDualCat - Constructable -

instance Exposable (SDualCat s o h x y) where
  type Form (SDualCat s o h x y) = PathSDualMap s o h x y
  form (SDualCat p) = p

instance Constructable (SDualCat s o h x y) where make = SDualCat . reduce

--------------------------------------------------------------------------------
-- SDualCat - Disjunctive -

instance Disjunctive2 (SDualCat s o h)    where variant2 = restrict variant2
instance Disjunctive (SDualCat s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- SDualCat - Category -

instance (Morphism h, ObjectClass h ~ s) => Morphism (SDualCat s o h) where
  type ObjectClass (SDualCat s o h) = s
  homomorphous (SDualCat p) = homomorphous p

instance (Morphism h, ObjectClass h ~ s) => Category (SDualCat s o h) where
  cOne = make . IdPath
  SDualCat f . SDualCat g = make (f . g)

--------------------------------------------------------------------------------
-- sctToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'ToDual'
-- in'SDualCat'.
sctToDualStruct ::Struct s x -> Struct s (o x) -> Variant2 Contravariant (SDualCat s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

-- | 'ToDual' as a 'Contravaraint' morphism in 'SDualCat'.
sctToDual :: Transformable1 o s => Struct s x -> Variant2 Contravariant (SDualCat s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

-- | prefixing a proxy.
sctToDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (SDualCat s o h) x (o x)
sctToDual' _ = sctToDual

--------------------------------------------------------------------------------
-- SDualCat - FunctorialG -

instance (Morphism h, ObjectClass h ~ s, ApplicativeG d h c, SDualisableG c s o d)
  => ApplicativeG d (SDualMap s o h) c where
  amapG (SDualMap h) = amapG h
  amapG t@ToDual     = toDualG (domain t)
  amapG f@FromDual   = fromDualG (range f)

instance ( Morphism h, ObjectClass h ~ s, ApplicativeG d h c, SDualisableG c s o d
         , TransformableGObjectClass d h c
         )
  => ApplicativeG d (SDualCat s o h) c where
  amapG = amapG . form

instance ( Morphism h, ObjectClass h ~ s, ApplicativeG d h c, SDualisableG c s o d
         , Category c, TransformableGObjectClass d h c
         )
  => ApplicativeGMorphism d (SDualCat s o h) c

instance ( Morphism h, ObjectClass h ~ s, ApplicativeG d h c, SDualisableG c s o d
         , Category c, TransformableGObjectClass d h c
         )
  => FunctorialG d (SDualCat s o h) c

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
toDualEither s (Left1 a)  = Right1 (sdlToDualLft s a)
toDualEither s (Right1 b) = Left1 (sdlToDualRgt s b)

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
-- implErrorSBidualisable -

-- | implementation error for 'SBiDualisable'
implErrorSBidualisable :: String -> AlgebraicException
implErrorSBidualisable f = ImplementationError ("SBiDualisable at: " ++ f)

--------------------------------------------------------------------------------
-- sdlToDualLft -

ff :: (Transformable1 o s, FunctorialG (SDual a b) (SDualCat s o h) (->))
  => q o h -> Struct s x -> a x -> b (o x)
ff q s a = case amapG toDual (SDual (Left1 a)) of
     SDual (Right1 b') -> b'
     _                 -> throw (implErrorSBidualisable "sdlToDualLft")
  where toDual = sctToDual' q s
