
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
-- Module      : OAlg.Hom.Oriented.X
-- Description : random variables for oriented homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- random variables for oriented homomorphisms.
module OAlg.Hom.Oriented.X
  ( xscmHomDisj
  )
  where

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Hom.Definition

--------------------------------------------------------------------------------
-- xscmHomDisj -

-- | random variable for some composable 'HomDisj'.
xscmHomDisj :: (TransformableG o s s, Morphism h, Transformable (ObjectClass h) s)
  => X (SomeObjectClass (SHom s s o h)) -> X (SomeMorphism h) -> X (SomeCmpb2 (HomDisj s o h))
xscmHomDisj xo = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomDisj f) (HomDisj g)) . xSctSomeCmpb2 10 xo

