
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
-- Module      : OAlg.Hom.Fibred.Definition
-- Description : homomorphisms between fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homomorphisms between 'Fibred' structures
module OAlg.Hom.Fibred.Definition
  ( -- * Fibred
    HomFibred, FunctorialFibred
  )
  where

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Structure.Fibred

import OAlg.Hom.Oriented.Definition

--------------------------------------------------------------------------------
-- HomFibred -

-- | homomorphisms between 'Fibred' structures.
--
-- __Property__ Let @'HomFibred' __h__@, then for all @__x__@, @__y__@ and @h@ in
-- @__h x y__@ holds:
--
-- (1) @'root' '.' 'amap' h '.=.' 'rmap' h '.' 'root'@.
class ( Morphism h, Applicative h, ApplicativeRoot h
      , Transformable (ObjectClass h) Fbr
      ) => HomFibred h where

instance HomFibred h => HomFibred (Path h)
instance TransformableFbr s => HomFibred (IdHom s)
instance TransformableFbr s => HomFibred (HomEmpty s)

--------------------------------------------------------------------------------
-- Functorialibred -

-- | functorial application of 'Fibred' homomorphisms.
type FunctorialFibred h = (HomFibred h, Functorial h, FunctorialRoot h)

