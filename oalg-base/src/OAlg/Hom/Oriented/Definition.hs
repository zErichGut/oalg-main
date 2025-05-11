
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.Hom.Oriented.Definition
-- Description : definition of homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Definition
  (
{-    
    -- * Hom Oriented    
    -- ** Disjunctive
    HomDisjunctiveOriented(..)
  , homOrtToDual', homOrtFromDual'
  , homOrtToCovariant
  , HomVariant

    -- ** Covariant
  , HomOriented, HomEmpty

    -- ** Applicative
  , ApplicativePoint, pmap, omap
  , FunctorialPoint

    -- ** Duality
  , SDualisableOriented
  , toDualArw, toDualPnt

    -- * Category Hom Oriented
  , HomOrt(..), homOrt

    -- ** Empty
  , HomOrtEmpty
  , homOrtToDualEmpty, homOrtFromDualEmpty

  , module V
-}
  )
  where

import Data.Kind

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.SDuality

import OAlg.Data.Proxy
import OAlg.Data.Identity
import OAlg.Data.Variant as V

import OAlg.Structure.Oriented hiding (Path(..))

--------------------------------------------------------------------------------
-- ApplicativePoint -

-- | applications on 'Point's.
type ApplicativePoint h = ApplicativeG Pnt h (->)

--------------------------------------------------------------------------------
-- pmap -

-- | the induced mapping of 'Point's given by 'amapG'. 
pmap :: ApplicativePoint h => h x y -> Point x -> Point y
pmap h = fromPntG (amapG h)

--------------------------------------------------------------------------------
-- omap -

-- | the induced mapping of 'Orientation'.
omap :: ApplicativePoint h => h a b -> Orientation (Point a) -> Orientation (Point b)
omap = amapG . pmap

--------------------------------------------------------------------------------
-- FunctorialPoint -

type FunctorialPoint h = FunctorialG Pnt h (->)

--------------------------------------------------------------------------------
-- HomOriented -

-- | covariant homomorphisms between 'Oriented' structures.
--
-- __Property__ Let @__h__@ be an instance of 'HomOriented', then
-- for all  @__a__@, @__b__@ and @h@ in @__h a b__@ holds:
--
-- (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
-- (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
class ( Morphism h, Applicative h, ApplicativePoint h
      , Transformable (ObjectClass h) Ort
      ) => HomOriented h where

instance HomOriented h => HomOriented (Path h)

--------------------------------------------------------------------------------
-- HomEmpty -

-- | the empty homomorphism.
newtype HomEmpty s x y = HomEmpty (EntEmpty2 x y)
  deriving (Show, Show2,Eq,Eq2,EqExt,Validable,Validable2)

--------------------------------------------------------------------------------
-- fromHomEmpty -

fromHomEmpty :: HomEmpty s a b -> x
fromHomEmpty (HomEmpty e) = fromEmpty2 e

--------------------------------------------------------------------------------
-- HomEmpty - Instances -

instance ApplicativeG t (HomEmpty s) c where amapG = fromHomEmpty

--------------------------------------------------------------------------------
-- HomEmpty - HomOriented -

instance Morphism (HomEmpty s) where
  type ObjectClass (HomEmpty s) = s
  domain = fromHomEmpty
  range  = fromHomEmpty

instance TransformableOrt s => HomOriented (HomEmpty s)

--------------------------------------------------------------------------------
-- HomVariant -

-- | 'Variant' for homs.
type HomVariant = Variant2

--------------------------------------------------------------------------------
-- HomDisjunctiveOriented -

-- | disjunctive homomorphism between 'Oriented' structures.
--
-- __Properties__ Let @'HomDisjunctiveOriented' __s o h__@, then holds:
--
-- (1) For all @__x__@ and @s@ in @'Struct' __s x__@ holds:
--
--     (1) @'homOrtFromDual' s '.' 'homOrtToDual' s '.=.' 'cOne' s@.
--
--     (2) @'homOrtToDual' s '.' 'homOrtFromDual' s '.=.' 'cOne' ('tau1' s)@.
--
-- (2) For all @__x__@, @__y__@ and @h@ in @__h x y__@ holds:
--
--     (1) If @'variant2' h '==' 'Covariant'@ then holds:
--
--         (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'start'@.
--
--         (2) @'end' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--     (2) If @'variant2' h '==' 'Contravariant'@ then holds:
--
--         (1) @'start' '.' 'amap' h '.=.' 'pmap' h '.' 'end'@.
--
--         (2) @'end' ',' 'amap' h '.=.' 'pmap' h '.' 'start'@.
class ( CategoryDisjunctive h
      , Functorial h, FunctorialPoint h
      , Transformable (ObjectClass h) Ort, Transformable1 o (ObjectClass h)
      )
  => HomDisjunctiveOriented o h where
  homOrtToDual :: Struct Ort x -> HomVariant Contravariant h x (o x)
  homOrtFromDual :: Struct Ort x -> HomVariant Contravariant h (o x) x

--------------------------------------------------------------------------------
-- homOrtToDual' -

homOrtToDual' :: HomDisjunctiveOriented o h
  => q o h -> Struct Ort x -> HomVariant Contravariant h x (o x)
homOrtToDual' _ = homOrtToDual

--------------------------------------------------------------------------------
-- homOrtToCovariant -

-- | mapping of a 'Contravariant' homomorphism to its 'Covariant' counter part via
-- composition from the left with 'homOrtToDual'.
homOrtToCovariant :: HomDisjunctiveOriented o h
  => q o
  -> HomVariant Contravariant h x y -> HomVariant Covariant h x (o y)
homOrtToCovariant q h = toCov (q' q h) (tau (range h)) h where
  q' :: q (o :: Type -> Type) -> HomVariant Contravariant h x y -> Proxy2 o h
  q' _ _ = Proxy2
  
  toCov :: HomDisjunctiveOriented o h
    => q o h -> Struct Ort y
    -> HomVariant Contravariant h x y -> HomVariant Covariant h x (o y)
  toCov q s (Contravariant2 h) = Covariant2 (t . h) where
    Contravariant2 t = homOrtToDual' q s

--------------------------------------------------------------------------------
-- homOrtFromDual -

homOrtFromDual' :: HomDisjunctiveOriented o h
  => q o h -> Struct Ort x -> HomVariant Contravariant h (o x) x
homOrtFromDual' _ = homOrtFromDual

--------------------------------------------------------------------------------
-- HomOrt -

newtype HomOrt s o h x y = HomOrt (SDualityCategory Ort s o h x y)
  deriving (Show,Show2,Disjunctive,Disjunctive2,CategoryDisjunctive)

deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq (HomOrt s o h x y)
deriving instance (Morphism h, Transformable s Typ, Eq2 h) => Eq2 (HomOrt s o h)

--------------------------------------------------------------------------------
-- HomOrt - Category -

instance Morphism h => Morphism (HomOrt s o h) where
  type ObjectClass (HomOrt s o h) = s
  homomorphous (HomOrt h) = homomorphous h

instance Morphism h => Category (HomOrt s o h) where
  cOne = HomOrt . cOne
  HomOrt f . HomOrt g = HomOrt (f . g)

--------------------------------------------------------------------------------
-- HomOrt - Functorial -

instance ( Morphism h, ApplicativeG d h c
         , DualisableG Ort c o d
         , Transformable s Ort
         , TransformableGObjectClassRange d s c
         )
  => ApplicativeG d (HomOrt s o h) c where
  amapG (HomOrt h) = amapG h


instance ( Morphism h, ApplicativeG d h c
         , DualisableG Ort c o d
         , Transformable s Ort
         , TransformableGObjectClassRange d s c
         )
  => ApplicativeGMorphism d (HomOrt s o h) c

instance ( Morphism h, ApplicativeG d h c
         , DualisableG Ort c o d
         , Transformable s Ort
         , TransformableGObjectClassRange d s c
         )
  => FunctorialG d (HomOrt s o h) c

--------------------------------------------------------------------------------
-- SDualisableOriented -

-- | duality according to @__o__@ on @__s__@-structured 'Oriented' types,
--
-- __Properties__ Let @'SDualisableOriented' __o s__@ then for all @__x__@
-- and @s@ in @'Struct' __s x__@ holds:
-- 
-- (1) @'start' '.' 'toDualArw' q '.=.' 'toDualPnt' q '.' 'end'@.
--
-- (2) @'end' '.' 'toDualArw' q '==' 'toDualPnt' q '.' 'start'@.
--
-- where @q@ is any proxy for @__o__@.
class ( DualisableG Ort (->) o Id, DualisableG Ort (->) o Pnt
      , Transformable s Ort, Transformable1 o s   
      ) => SDualisableOriented o s

instance (TransformableOrt s, TransformableOp s) => SDualisableOriented Op s
{-
--------------------------------------------------------------------------------
-- toDualArw -

-- | the dual arrow induced by @'DualisableG (->) __o__ 'Id'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualArw :: SDualisableOriented o s => q o -> Struct s x -> x -> o x
toDualArw q s = fromIdG (toDualG' (d q s) s (tau s)) where
  d :: SDualisableOriented o s => q o -> Struct s x -> Struct Ort x -> SDualityG Ort (->) o Id
  d _ _ _ = SDualityG

--------------------------------------------------------------------------------
-- toDualPnt -

-- | the dual point induced by @'DualisableG' (->) __o__ 'Pnt'@.
--
-- __Note__ The induced mapping is independent of @__s__@!
toDualPnt :: SDualisableOriented o s => q o -> Struct s x -> Point x -> Point (o x)
toDualPnt q s = fromPntG (toDualG' (d q s) (tauType s)) where
  d :: SDualisableOriented o s => q o -> Struct s x -> SDualityG (->) o Pnt
  d _ _ = SDualityG

--------------------------------------------------------------------------------
-- HomOrt - HomDisjunctiveOriented -

instance (HomOriented h, SDualisableOriented o s)
  => HomDisjunctiveOriented o (HomOrt s o h) where
  homOrtToDual s = Contravariant2 (HomOrt t) where Contravariant2 t = sctToDual s
  homOrtFromDual s = Contravariant2 (HomOrt f) where Contravariant2 f = sctFromDual s

--------------------------------------------------------------------------------
-- homOrtCov -

-- | embedding of 'HomOriented' to 'HomOrt'.
homOrt :: (HomOriented h, Transformable (ObjectClass h) s)
  => h x y -> HomVariant Covariant (HomOrt s o h) x y
homOrt = Covariant2 . HomOrt . sctCov

--------------------------------------------------------------------------------
-- HomOrtEmpty -

-- | shortcut.
type HomOrtEmpty s o = HomOrt s o (HomEmpty s)

--------------------------------------------------------------------------------
-- homOrtToDualEmpty -

-- | the from 'homOrtToDual' induced morphism 
homOrtToDualEmpty :: (SDualisableOriented o s, TransformableOrt s)
  => Struct s x -> HomVariant Contravariant (HomOrtEmpty s o) x (o x)
homOrtToDualEmpty = homOrtToDual


--------------------------------------------------------------------------------
-- homOrtFromDualEmpty -

-- | the from 'homOrtFromDual' indueced morphism.
homOrtFromDualEmpty :: (SDualisableOriented o s, TransformableOrt s)
  => Struct s x -> HomVariant Contravariant (HomOrtEmpty s o) (o x) x
homOrtFromDualEmpty = homOrtFromDual
-}
