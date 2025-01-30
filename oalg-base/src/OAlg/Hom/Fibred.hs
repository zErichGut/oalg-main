
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Hom.Oriented
-- Description : homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred
  ( -- * Fibred
    HomFibred(..), FunctorialHomFibred

    -- * Fibred Oriented
  , HomFibredOriented

    -- * Proposition
  , prpHomFbrOrt
  )
  where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented.Definition hiding (Path(..))

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomFibred -

-- | type family of homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @h@ be an instance of 'HomFibred' then for all @__a__@, @__b__@ and @f@ in
-- @__h__ __a__ __b__@ and @x@ in @__a__@ holds: @'root' ('amap' f x) '==' 'rmap' f ('root' x)@.
class ( Morphism h, Applicative h, Transformable (ObjectClass h) Fbr
      , Transformable (ObjectClass h) Typ
      ) => HomFibred h where
  rmap :: h a b -> Root a -> Root b

  default rmap :: (Transformable (ObjectClass h) FbrOrt, HomOriented h)
               => h a b -> Root a -> Root b
  rmap h = rmap' (tauHom (homomorphous h)) h where

    rmap' :: HomOriented h => Homomorphous FbrOrt a b -> h a b -> Root a -> Root b
    rmap' (Struct :>: Struct) = omap

instance HomFibred h => HomFibred (Path h) where
  rmap (IdPath _) r = r
  rmap (f :. pth) r = rmap f $ rmap pth r

--------------------------------------------------------------------------------
-- FunctorialHomFibred -

-- | functorial application of 'Fibred' homomorphisms.
class (Category h, Functorial h, HomFibred h) => FunctorialHomFibred h

instance FunctorialHomFibred h => FunctorialHomFibred (Path h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Fbr h = HomFibred h

--------------------------------------------------------------------------------
-- HomFibredOriented -

-- | type family of homomorphisms between 'FibredOriented' structures.
--
-- __Property__ Let @h@ be an instance of 'HomFibredOriented' then for all @__a__@, @__b__@ and @f@ in
-- @__h__ __a__ __b__@ and @r@ in @'Root' __a__@ holds: @'rmap' f r '==' 'omap' f r@.
class (HomOriented h , HomFibred h, Transformable (ObjectClass h) FbrOrt)
  => HomFibredOriented h

instance HomFibredOriented h => HomFibredOriented (Path h)

--------------------------------------------------------------------------------
-- prpHomFbrOrt -

relHomFbrOrtHomomorphous :: (HomFibredOriented h, Show2 h)
  => Homomorphous FbrOrt a b -> h a b -> Root a -> Statement
relHomFbrOrtHomomorphous (Struct :>: Struct) f r
  = (rmap f r == omap f r) :?> Params ["f":=show2 f,"r":=show r]

-- | validity according to 'HomFibredOriented'.
prpHomFbrOrt :: (HomFibredOriented h, Show2 h) => h a b -> Root a -> Statement
prpHomFbrOrt f r = Prp "HomFbrOrt"
  :<=>: relHomFbrOrtHomomorphous (tauHom (homomorphous f)) f r

--------------------------------------------------------------------------------
-- Hom -

type instance Hom FbrOrt h = HomFibredOriented h

--------------------------------------------------------------------------------
-- IdHom - Hom -

instance (TransformableFbr s, TransformableTyp s) => HomFibred (IdHom s) where
  rmap IdHom r = r
  
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s, TransformableTyp s
         )
  => HomFibredOriented (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s, Typeable s
         )
  => HomFibred (HomOp s)
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s, Typeable s
         )
  => HomFibredOriented (HomOp s)
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s, Typeable s
         )
  => HomFibred (IsoOp s)
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s, Typeable s
         )
  => HomFibredOriented (IsoOp s)

--------------------------------------------------------------------------------
-- OpHom -

instance HomFibredOriented h => HomFibred (OpHom h)
instance HomFibredOriented h => HomFibredOriented (OpHom h)

