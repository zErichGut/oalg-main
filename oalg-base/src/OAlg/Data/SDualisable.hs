
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
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
  ( -- * Dualisable
    SDualisable, sdlToDual
  ) where

import OAlg.Prelude

import OAlg.Category.SDual

import OAlg.Data.Identity
import OAlg.Data.Variant

--------------------------------------------------------------------------------
-- SDualisable -

type SDualisable s o h = (Transformable1 o s, FunctorialG Id (CatSDual s o h) (->))

--------------------------------------------------------------------------------
-- sdlToDual -

sdlToDual :: SDualisable s o h => q h o -> Struct s x -> x -> o x
sdlToDual q s = fromIdG $ amapG toDual where Contravariant2 toDual = sctToDual' q s





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


