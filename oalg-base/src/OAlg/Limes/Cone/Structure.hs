
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}



-- |
-- Module      : OAlg.Limes.Cone.Structure
-- Description : definition of eligible cone structures.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of eligible cone structures.
module OAlg.Limes.Cone.Structure
  (
    -- * Cone Struct
    ConeStruct(..), cnStructOp, cnStructMlt, cnStruct
  , cnStructMltOrDst
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive

--------------------------------------------------------------------------------
-- ConeStruct -

-- | cone structures.
data ConeStruct s a where
  ConeStructMlt :: Multiplicative a => ConeStruct Mlt a
  ConeStructDst :: Distributive a => ConeStruct Dst a

deriving instance Show (ConeStruct s a)
deriving instance Eq (ConeStruct s a)

--------------------------------------------------------------------------------
-- cnStructOp -

-- | the opposite cone structure.
cnStructOp :: ConeStruct s a -> ConeStruct s (Op a)
cnStructOp cs = case cs of
  ConeStructMlt -> ConeStructMlt
  ConeStructDst -> ConeStructDst

--------------------------------------------------------------------------------
-- cnStructMlt -

-- | the 'Multiplicative' structure of a cone structure.
cnStructMlt :: ConeStruct s a -> Struct Mlt a
cnStructMlt cs = case cs of
  ConeStructMlt -> Struct
  ConeStructDst -> Struct

--------------------------------------------------------------------------------
-- cnStruct -

-- | the associated structure of a cone structure.
cnStruct :: ConeStruct s a -> Struct s a
cnStruct cs = case cs of
  ConeStructMlt -> Struct
  ConeStructDst -> Struct

--------------------------------------------------------------------------------
-- cnStructMltOrDst -

-- | proof of @__s__@ being either 'Mlt' or 'Dst'.
cnStructMltOrDst :: ConeStruct s a -> Either (s :~: Mlt) (s :~: Dst)
cnStructMltOrDst cs = case cs of
  ConeStructMlt -> Left Refl
  ConeStructDst -> Right Refl

