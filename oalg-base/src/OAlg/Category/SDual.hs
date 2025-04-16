
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
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
    CatSDual(), sctToDual
    
    -- * Map
  , MapSDual(..)
  , PathMapSDual, rdcPathMapSDual
  -- , MapSDualApplicative, MapSDualApplicative1

    -- * Duality
  -- , CatSDualDuality, CatSDualDuality1

  ) where

import Control.Monad

import Data.Typeable
import Data.List ((++))

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- MapSDual -

-- | adjoining to a type family @__h__@ of morphisms two auxiliary morphisms 'ToDual' and 'FromDual'.
data MapSDual s o h x y where
  MapSDual :: Transformable (ObjectClass h) s => h x y -> MapSDual s o h x y
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

instance Morphism h => Morphism (MapSDual s o h) where
  type ObjectClass (MapSDual s o h) = s

  homomorphous (MapSDual h) = tauHom (homomorphous h)
  homomorphous ToDual       = Struct :>: Struct
  homomorphous FromDual     = Struct :>: Struct

instance Transformable s Typ => TransformableObjectClassTyp (MapSDual s o h)

{-
--------------------------------------------------------------------------------
-- MapSDual - Applicative -

instance (Morphism h, Applicative h, SDualisable s o) => Applicative (MapSDual s o h) where
  amap (MapSDual h) = amap h
  amap t@ToDual     = sdlToDual (domain t)
  amap f@FromDual   = sdlFromDual (range f)

--------------------------------------------------------------------------------
-- SDual -
newtype SDual (r :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type) s (o :: Type -> Type)
  a b x = SDual (Either1 a b x)

sdlRefl1 :: SReflexive1 r s o a b => SDual r s o a b x -> r o a b
sdlRefl1 (SDual _) = unit


sctMapCvt :: (Applicative1 h a, Applicative1 h b) => h x y -> SDual r s o a b x -> SDual r s o a b y
sctMapCvt h (SDual ab) = SDual $ case ab of
  Left1 a             -> Left1 $ amap1 h a
  Right1 b            -> Right1 $ amap1 h b

sctToDual :: SReflexive1 r s o a b => Struct s x -> SDual r s o a b x -> SDual r s o a b (o x)
sctToDual s d@(SDual ab) = SDual $ case ab of
  Left1 a             -> Right1 $ sdlToDualLeft r s a
  Right1 b            -> Left1 $ sdlToDualRight r s b
  where r = sdlRefl1 d 


sctFromDual :: SDualisable1 s o a b => Struct s x -> SDual a b (o x) -> SDual a b x
sctFromDual s (SDual ab) = SDual $ case ab of
  Left1 a'              -> Right1 $ sdlFromDualLeft s a'
  Right1 b'             -> Left1 $ sdlFromDualRight s b'

----------------------------------------
-- MapSDual - Applicative1 -


instance (Morphism h, Applicative1 h a, Applicative1 h b, SReflexive1 r s o a b)
  => Applicative1 (MapSDual s o h) (SDual r s o a b) where
  amap1 (MapSDual h) = sctMapCvt h
  amap1 t@ToDual     = sctToDual (domain t)
  amap1 f@FromDual   = error "nyi" -- sctFromDual (range f)
-}  

--------------------------------------------------------------------------------
-- PathMapSDual -

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

newtype CatSDual s o h x y = CatSDual (PathMapSDual s o h x y)
  deriving (Show, Show2, Validable, Validable2)

deriving instance (Morphism h, TransformableTyp s, Eq2 h) => Eq2 (CatSDual s o h)

instance (Morphism h, Entity2 h, TransformableTyp s, Typeable o, Typeable s)
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

instance Morphism h => Morphism (CatSDual s o h) where
  type ObjectClass (CatSDual s o h) = s
  homomorphous (CatSDual p) = homomorphous p

instance Morphism h => Category (CatSDual s o h) where
  cOne = make . IdPath
  CatSDual f . CatSDual g = make (f . g)



--------------------------------------------------------------------------------
-- sctToDual -

sctToDualStruct :: Struct s x -> Struct s (o x) -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDualStruct s@Struct Struct = Contravariant2 $ make (ToDual :. IdPath s)

sctToDual :: Transformable1 o s => Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual s = sctToDualStruct s (tau1 s)

{-
sctToDual' :: SDuality s o h a b -> Struct s x -> Variant2 Contravariant (CatSDual s o h) x (o x)
sctToDual' SDuality = sctToDual

--------------------------------------------------------------------------------
-- sctMap -

sctMap :: SDuality s o h a b -> Variant2 v (CatSDual s o h) x y -> SDual a b x -> SDual a b y
sctMap SDuality = amap1

--------------------------------------------------------------------------------
-- SDuality -

data SDuality s o h a b where
  SDuality
    :: (Transformable1 o s, Functorial1 (CatSDual s o h) (SDual a b))
    => SDuality s o h a b

--------------------------------------------------------------------------------
-- sctToDualLeft -

sctToDualLeft :: SDuality s o h a b -> Struct s x -> a x -> b (o x)
sctToDualLeft d s a = case sctMap d (sctToDual' d s) (SDual (Left1 a)) of
  SDual a'         -> case a' of
    Right1 bo      -> bo
    _              -> throw $ ImplementationError "sctToDualLeft"
    -- this error occurs if you allow overlapping instances for
    -- Applicative1 (CatSDual s o h) (SDual a b) which yields to a
    -- non valid sctMap!!!

-}


{-
--------------------------------------------------------------------------------
-- SDuality -

-- | duality of 1-parameterized types over @__s__@-structured types.
--
-- __Property__ Let @d@ be in @'SDuality' __s o h a b__@. then for all @h@ in
-- @'CatSDual' __s o h x y__@ and @s@ in @'Struct' __s x__@ holds:
--
-- (1) If @'variant' h '==' 'Covariant'@ then holds:
--
--     (1) for all @a@ in @__a x__@ holds:
--     @'amap1' h ('Left1' a)@ matches @'Left1' a'@ for some @a'@ in @__a y__@.
--
--     (2) for all @b@ in @__b x__@ holds:
--     @'amap1' h ('Right1' b)@ matches @'Right' b'@ for some @b'@ in @__b y__@.
--
-- (2) If @'variant' h '==' 'Contravariant'@ then holds:
--
--     (1) for all @a@ in @__a x__@ holds:
--     @'amap1' h ('Left1' a)@ matches @'Right1' b'@ for some @b'@ in @__b y__@.
--
--     (2) for all @b@ in @__b x__@ holds:
--     @'amap1' h ('Right1' b)@ matches @'Left1' a'@ for some @a'@ in @__a y__@.
data SDuality s o h a b where
  SDuality :: (Transformable1 o s, Applicative1 (CatSDual s o h) (Either1 a b))
           => SDuality s o h a b

--------------------------------------------------------------------------------
-- prpSDuality -

prpSDuality :: (Show1 a, Show1 b)
  => SDuality s o h a b -> CatSDual s o h x y
  -> Struct s x -> X (Either1 a b x) -> Statement
prpSDuality SDuality h Struct xab = Prp "SDuality" :<=>: Forall xab
  (\ab            -> case variant h of
    Covariant     -> case ab of
      Left1 _     -> case amap1 h ab of
        Left1 _   -> SValid
        Right1 _  -> Label "1.1" :<=>: False :?> Params ["ab":=show1 ab]
      Right1 _    -> case amap1 h ab of
        Left1 _   -> Label "1.2" :<=>: False  :?> Params ["ab":=show1 ab]
        Right1 _  -> SValid
    Contravariant -> case ab of
      Left1 _     -> case amap1 h ab of
        Left1 _   -> Label "2.1" :<=>: False :?> Params ["ab":=show1 ab]
        Right1 _  -> SValid
      Right1 _    -> case amap1 h ab of
        Left1 _   -> SValid
        Right1 _  -> Label "1.2" :<=>: False  :?> Params ["ab":=show1 ab]
  )
-}


