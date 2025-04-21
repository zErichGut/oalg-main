
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , FunctionalDependencies
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , ConstraintKinds
#-}

-- |
-- Module      : OAlg.Category.SDual
-- Description : category for structural dualities.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- category for structural dualities.
module OAlg.Category.SDual
  (
    -- * Category
    CatSDual(), sctToDual, sctToDual'
    
    -- * Map
  , MapSDual(..)
  , PathMapSDual, rdcPathMapSDual
    
    -- * Structural Duality
    -- ** SDualisable
  , SDualisable
  , sdlToDual
  , SReflexive(..), fromDualG

    -- ** SDualisable1
  , SDualisable1, SDual(..)
  , sdlToDualLeft

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
-- MapSDual -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data MapSDual s o h x y where
  MapSDual :: (Morphism h, ObjectClass h ~ s) => h x y -> MapSDual s o h x y
  ToDual   :: (Structure s x, Structure s (o x)) => MapSDual s o h x (o x)
  FromDual :: (Structure s x, Structure s (o x)) => MapSDual s o h (o x) x

--------------------------------------------------------------------------------
-- MapSDual - Disjunctive -

instance Disjunctive (MapSDual s o h x y) where
  variant (MapSDual _) = Covariant
  variant _            = Contravariant

instance Disjunctive2 (MapSDual s o h)

--------------------------------------------------------------------------------
-- MapSDual - Entity2 -

instance Show2 h => Show2 (MapSDual s o h) where
  show2 (MapSDual h) = "MapSDual (" ++ show2 h ++ ")"
  show2 ToDual       = "ToDual"
  show2 FromDual     = "FromDual"

instance Eq2 h => Eq2 (MapSDual s o h) where
  eq2 (MapSDual f) (MapSDual g) = eq2 f g
  eq2 ToDual ToDual             = True
  eq2 FromDual FromDual         = True
  eq2 _ _                       = False

instance Validable2 h => Validable2 (MapSDual s o h) where
  valid2 (MapSDual h) = valid2 h
  valid2 _            = SValid

instance (Entity2 h, Typeable s, Typeable o) => Entity2 (MapSDual s o h)

--------------------------------------------------------------------------------
-- MapSDual - Morphism -

instance Morphism (MapSDual s o h) where
  type ObjectClass (MapSDual s o h) = s

  homomorphous (MapSDual h) = homomorphous h
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance Transformable s Typ => TransformableObjectClassTyp (MapSDual s o h)

--------------------------------------------------------------------------------
-- PathMapSDual -

-- | path of 'MapSDual'.
type PathMapSDual s o h = Path (MapSDual s o h)

--------------------------------------------------------------------------------
-- rdcPathMapSDual -

rdcPathMapSDual :: PathMapSDual s o h x y -> Rdc (PathMapSDual s o h x y)
rdcPathMapSDual p = case p of
  FromDual :. ToDual :. p' -> reducesTo p' >>= rdcPathMapSDual
  ToDual :. FromDual :. p' -> reducesTo p' >>= rdcPathMapSDual
  p' :. p''                -> rdcPathMapSDual p'' >>= return . (p' :.)
  _                        -> return p

instance Reducible (PathMapSDual s o h x y) where
  reduce = reduceWith rdcPathMapSDual

--------------------------------------------------------------------------------
-- CatSDual -

-- | category for structural dualities.
newtype CatSDual s o h x y = CatSDual (PathMapSDual s o h x y)
  deriving (Show, Show2, Validable, Validable2)

deriving instance (TransformableTyp s, Eq2 h) => Eq2 (CatSDual s o h)

instance (Entity2 h, TransformableTyp s, Typeable o, Typeable s)
  => Entity2 (CatSDual s o h)

--------------------------------------------------------------------------------
-- CatSDual - Disjunctive -

instance Disjunctive2 (CatSDual s o h)    where variant2 = restrict variant2
instance Disjunctive (CatSDual s o h x y) where variant  = restrict variant

--------------------------------------------------------------------------------
-- CatSDual - Constructable -

instance Exposable (CatSDual s o h x y) where
  type Form (CatSDual s o h x y) = PathMapSDual s o h x y
  form (CatSDual p) = p

instance Constructable (CatSDual s o h x y) where make = CatSDual . reduce

--------------------------------------------------------------------------------
-- CatSDual - Category -

instance Morphism (CatSDual s o h) where
  type ObjectClass (CatSDual s o h) = s
  homomorphous (CatSDual p) = homomorphous p

instance Category (CatSDual s o h) where
  cOne = make . IdPath
  CatSDual f . CatSDual g = make (f . g)

--------------------------------------------------------------------------------
-- sctToDual -

-- | using the structural constraints to constract the 'Contravariant' morphism of 'ToDual'
-- in'CatSDual'.
sctToDualStruct :: Struct s x -> Struct s (o x) -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

-- | 'ToDual' as a 'Contravaraint' morphism in 'CatSDual'.
sctToDual :: Transformable1 o s => Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

-- | prefixing a proxy.
sctToDual' :: Transformable1 o s
  => q o h -> Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual' _ = sctToDual

--------------------------------------------------------------------------------
-- SReflexive -

-- | duality of @__s__@-structured types given by a reflection.
--
-- __Property__ Let @'SReflexive' __c s o d__@, then for all @__x__@ and @s@ in @'Struct' __s x__@
-- holds:
--
-- (1) @'toDualG'' q s' '.' 'toDualG'' q s '.=.' u@.
--
-- (2) @'toDualG'' q s '.' v '.=.' v' . 'toDualG'' q s''@.
--
-- where @q@ is any proxy in @__q c s o d__@, @s' = 'tau1' s@ , @s'' = 'tau1' s'@,
-- @'Inv2' u v = 'relfG'' q s@ and @'Inv2' _ v' = 'reflG'' q s'@.
--
-- __Note__ The properties above imply that @'toDualG' s@ and @'fromDualG' s@ are inverse
-- in @__c__@ for all @__x__@ and @s@ in @'Struct' __s x__@ and hence establish a duality
-- within @__s__@ structured types.
class (Category c, Transformable1 o s, TransformableG d s (ObjectClass c))
  => SReflexive c s o d where
  toDualG :: Struct s x -> c (d x) (d (o x))
  reflG :: Struct s x -> Inv2 c (d x) (d (o (o x)))

instance TransformableGObjectClassRange d s c => TransformableGObjectClass d (MapSDual s o h) c

--------------------------------------------------------------------------------
-- SReflection -

-- | attest of being 'SReflexive'.
data SReflection c s o d where SReflection :: SReflexive c s o d => SReflection c s o d

--------------------------------------------------------------------------------
-- toDualG' -

-- | prefixing a proxy.
toDualG' :: SReflexive c s o d => q c s o d -> Struct s x -> c (d x) (d (o x))
toDualG' _ = toDualG

--------------------------------------------------------------------------------
-- reflG' -

-- | prefixing a proxy.
reflG' :: SReflexive c s o d => q c s o d -> Struct s x -> Inv2 c (d x) (d (o (o x)))
reflG' _ = reflG

--------------------------------------------------------------------------------
-- prpSReflexive -

-- | validity according to 'SReflexive'.
prpSReflexive :: SReflexive c s o d
  => EqExt c
  => q c s o d -> Struct s x -> Statement
prpSReflexive q s = Prp "SReflexive" :<=>:
  And [ Label "1" :<=>: (toDualG' q s' . toDualG' q s .=. u)
      , Label "2" :<=>: (toDualG' q s . v .=. v' . toDualG' q s'')
      ]
  where s'        = tau1 s
        s''       = tau1 s' 
        Inv2 u v  = reflG' q s
        Inv2 _ v' = reflG' q s'

--------------------------------------------------------------------------------
-- fromDualG -

fromDualG :: SReflexive c s o d => Struct s x -> c (d (o x)) (d x)
fromDualG s = v . toDualG (tau1 s) where Inv2 _ v = reflG s

--------------------------------------------------------------------------------
-- SReflexive - Instances -

instance Transformable1 Op s => SReflexive (->) s Op Id where
  toDualG _ = toIdG Op 
  reflG _   = Inv2 (amap1 (Op . Op)) (amap1 (fromOp . fromOp))
  
--------------------------------------------------------------------------------
-- CatSDual - FunctorialG -

instance (ApplicativeG d h c, SReflexive c s o d)
  => ApplicativeG d (MapSDual s o h) c where
  amapG (MapSDual h) = amapG h
  amapG t@ToDual     = toDualG (domain t)
  amapG f@FromDual   = fromDualG (range f)

instance (ApplicativeG d h c, SReflexive c s o d, TransformableGObjectClassRange d s c)
  => ApplicativeG d (CatSDual s o h) c where
  amapG = amapG . form


instance (ApplicativeG d h c, SReflexive c s o d, TransformableGObjectClassRange d s c)
  => FunctorialG d (CatSDual s o h) c

--------------------------------------------------------------------------------
-- SDualisable -

type SDualisable s o h = (Transformable1 o s, FunctorialG Id (CatSDual s o h) (->))

--------------------------------------------------------------------------------
-- sdlToDual -

sdlToDual :: SDualisable s o h => q o h -> Struct s x -> x -> o x
sdlToDual q s = fromIdG $ amapG toDual where Contravariant2 toDual = sctToDual' q s

--------------------------------------------------------------------------------
-- SReflexiveBi -

class ( Category c, Transformable1 o s
      , TransformableG a s (ObjectClass c)
      , TransformableG b s (ObjectClass c)
      )
  => SReflexiveBi c s o a b | a -> b, b -> a where
  toDualLft :: Struct s x -> c (a x) (b (o x))
  toDualRgt :: Struct s x -> c (b x) (a (o x))
  reflLft :: Struct s x -> Inv2 c (a x) (a (o (o x)))
  reflRgt :: Struct s x -> Inv2 c (b x) (b (o (o x)))

--------------------------------------------------------------------------------
-- fromDualLft -

fromDualLft :: SReflexiveBi c s o a b => Struct s x -> c (b (o x)) (a x)
fromDualLft s = v . toDualRgt (tau1 s) where Inv2 _ v = reflLft s

--------------------------------------------------------------------------------
-- fromDualRgt -

fromDualRgt :: SReflexiveBi c s o a b => Struct s x -> c (a (o x)) (b x)
fromDualRgt s = v . toDualLft (tau1 s) where Inv2 _ v = reflRgt s

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

toDualEither :: SReflexiveBi (->) s o a b => Struct s x -> Either1 a b x -> Either1 a b (o x)
toDualEither s (Left1 a)  = Right1 (toDualLft s a)
toDualEither s (Right1 b) = Left1 (toDualRgt s b)

--------------------------------------------------------------------------------
-- reflEitherTo -

reflEitherTo :: SReflexiveBi (->) s o a b
  => Struct s x -> (->) (Either1 a b x) (Either1 a b (o (o x)))
reflEitherTo s (Left1 a)  = Left1 (u a)  where Inv2 u _ = reflLft s
reflEitherTo s (Right1 b) = Right1 (u b) where Inv2 u _ = reflRgt s 

--------------------------------------------------------------------------------
-- reflEitherFrom -

reflEitherFrom :: SReflexiveBi (->) s o a b
  => Struct s x -> (->) (Either1 a b (o (o x))) (Either1 a b x)
reflEitherFrom s (Left1 a'') = Left1 (v a'') where Inv2 _ v   = reflLft s
reflEitherFrom s (Right1 b'') = Right1 (v b'') where Inv2 _ v = reflRgt s


------------------------------------------------------------------------------------------
-- SDual - Reflexive -

instance SReflexiveBi (->) s o a b => SReflexive (->) s o (SDual a b) where
  toDualG s = SDual . toDualEither s . fromSDual

  reflG s = Inv2 u v where
    u = SDual . reflEitherTo s . fromSDual
    v = SDual . reflEitherFrom s . fromSDual

instance (ApplicativeG a h (->), ApplicativeG b h (->)) => ApplicativeG (SDual a b) h (->) where
  amapG h = SDual . amapEither h . fromSDual

--------------------------------------------------------------------------------
-- SDualisable1 -

type SDualisable1 s o h a b = (Transformable1 o s, FunctorialG (SDual a b) (CatSDual s o h) (->))

--------------------------------------------------------------------------------
-- implErrorOverlappingInstances -

-- | implementation error arising from overlapping instances for
-- @'FunctorialG' ('SDual' __a b__) ('CatSDual' __s o h__) ('->')@.
implErrorOverlappingInstances :: AlgebraicException
implErrorOverlappingInstances = ImplementationError
                              ( "arising from overlapping instances for "
                              ++ "FunctorialG (SDual a b) (CatSDual s o h) (->)"
                              )
                             
--------------------------------------------------------------------------------
-- sdlToDualLeft -

sdlToDualLeft :: SDualisable1 s o h a b => q a b o h -> Struct s x -> a x -> b (o x)
sdlToDualLeft q s = \a -> case amapG toDual (SDual (Left1 a)) of
     SDual (Right1 b') -> b'
     _                 -> throw implErrorOverlappingInstances
  where Contravariant2 toDual = sctToDual' q s

