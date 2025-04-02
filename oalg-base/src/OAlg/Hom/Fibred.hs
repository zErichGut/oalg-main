
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds  #-}

-- |
-- Module      : OAlg.Hom.Oriented
-- Description : homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred
  (
    -- * Fibred
    HomFibred, FunctorialHomFibred

    -- * Applications
  , ApplicativeRoot(..), FunctorialRoot
  
    -- * Fibred Oriented
  , HomFibredOriented

    -- * Proposition
  , prpHomFbrOrt
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred
import OAlg.Structure.Oriented.Definition hiding (Path(..))

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- ApplicativeRoot -

-- | applications on 'Root's.
class ApplicativeRoot h where
  rmap :: h a b -> Root a -> Root b

  default rmap :: (Morphism h, Transformable (ObjectClass h) FbrOrt, ApplicativePoint h)
               => h a b -> Root a -> Root b
  rmap h = rmap' (tauHom (homomorphous h)) h where

    rmap' :: ApplicativePoint h => Homomorphous FbrOrt a b -> h a b -> Root a -> Root b
    rmap' (Struct :>: Struct) = omap

instance ApplicativeRoot h => ApplicativeRoot (Path h) where
  rmap (IdPath _) r = r
  rmap (f :. pth) r = rmap f $ rmap pth r

--------------------------------------------------------------------------------
-- FunctorialRoot -

-- | functorial applications on 'Root's.
--
-- __Property__ Let @'FunctorialRoot' __h__@, then holds:
--
-- (1) For all @__a__@ and
-- @s@ in @'Struct' ('ObjectClass' __h__) __a__@ holds: @'rmap' ('cOne' s) '.=.' 'id'@.
--
-- (2) For all @__a__@, @__b__@, @__c__@, @f@ in @__h b c__@ and
-- @g@ in @__h a b__@ holds:
-- @'rmap' (f '.' g) '.=.' 'rmap' f '.' 'rmap' g@.
class (Category h, ApplicativeRoot h) => FunctorialRoot h

instance (Morphism h, ApplicativeRoot h) => FunctorialRoot (Path h)

--------------------------------------------------------------------------------
-- HomFibred -

-- | type family of homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @h@ be an instance of 'HomFibred' then for all @__a__@, @__b__@ and @f@ in
-- @__h__ __a__ __b__@ and @x@ in @__a__@ holds:
--
-- (1) @'root' '.' 'amap' f '.=.' 'rmap' f '.' 'root'@.
class ( Morphism h, Applicative h, ApplicativeRoot h
      , Transformable (ObjectClass h) Fbr, Transformable (ObjectClass h) Typ
      ) => HomFibred h where


instance HomFibred h => HomFibred (Path h)

--------------------------------------------------------------------------------
-- FunctorialHomFibred -

-- | functorial application of 'Fibred' homomorphisms.
type FunctorialHomFibred h = (HomFibred h, Functorial h, FunctorialRoot h)

--------------------------------------------------------------------------------
-- Hom -

type instance Hom Fbr h = HomFibred h

--------------------------------------------------------------------------------
-- HomFibredOriented -

-- | type family of homomorphisms between 'FibredOriented' structures.
--
-- __Property__ Let @'HomFibredOriented' __h__@, then holds:
--
-- (1) For all @__a__@, @__b__@ and @f@ in
-- @__h__ __a__ __b__@ holds: @'rmap' f '.=.' 'omap' f@.
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

instance ApplicativeRoot (IdHom s) where
  rmap IdHom r = r
  
instance (TransformableFbr s, TransformableTyp s) => HomFibred (IdHom s)
  
instance ( TransformableOp s, TransformableOrt s, TransformableFbr s
         , TransformableFbrOrt s, TransformableTyp s
         )
  => HomFibredOriented (IdHom s)

--------------------------------------------------------------------------------
-- IsoOp - Hom -

instance TransformableFbrOrt s => ApplicativeRoot (HomOp s)

instance ( TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibred (HomOp s)


instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (HomOp s)

instance TransformableFbrOrt s => ApplicativeRoot (IsoOp s)

instance (TransformableFbr s, TransformableFbrOrt s, TransformableTyp s) => HomFibred (IsoOp s)

instance ( TransformableOp s, TransformableOrt s, TransformableFbr s, TransformableFbrOrt s
         , TransformableTyp s
         )
  => HomFibredOriented (IsoOp s)

--------------------------------------------------------------------------------
-- OpHom -

instance HomFibredOriented h => ApplicativeRoot (OpHom h)
instance HomFibredOriented h => HomFibred (OpHom h)
instance HomFibredOriented h => HomFibredOriented (OpHom h)


