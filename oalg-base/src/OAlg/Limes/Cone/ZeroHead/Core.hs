
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE GADTs, StandaloneDeriving #-}

-- |
-- Module      : OAlg.Limes.Cone.ZeroHead.Core
-- Description : basice definitions for cones with a first zero arrow. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basice definitions a 'Cone' with a first zero arrow. 
module OAlg.Limes.Cone.ZeroHead.Core
  (
    ConeZeroHead(..)
  ) where

import OAlg.Prelude

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Limes.Cone.Definition
import OAlg.Limes.Cone.Conic

--------------------------------------------------------------------------------
-- ConeZeroHead -

-- | predicate for cones where the first arrow of its underlying diagram is equal to 'zero'.
data ConeZeroHead s p d t n m x where
  ConeZeroHead :: Distributive x => Cone s p d t n (m+1) x -> ConeZeroHead s p d t n (m+1) x

deriving instance Show (d t n (S m) x) => Show (ConeZeroHead s p d t n (S m) x)
deriving instance Eq (d t n (S m) x) => Eq (ConeZeroHead s p d t n (S m) x)

instance Conic ConeZeroHead where cone (ConeZeroHead c) = c
  
--------------------------------------------------------------------------------
-- ConeZeroHead - Validable -

instance (Diagrammatic d, Validable (d t n (S m) x))
  => Validable (ConeZeroHead s p d t n (S m) x) where
  valid (ConeZeroHead c)
    = And [ valid c
          , relIsZero $ head $ dgArrows $ diagram $ diagrammaticObject c
          ]
