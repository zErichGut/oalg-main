
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Diagram.Quiver
-- Description : the underlying quiver of a diagram
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- the underlying 'Quiver' of a 'OAlg.Entity.Diagram.Definition.Diagram'.
module OAlg.Entity.Diagram.Quiver
  ( -- * Quiver
    Quiver(..), qvOrientations 

    -- * Duality
  , coQuiver, coQuiverInv
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented

import OAlg.Entity.Natural
import OAlg.Entity.FinList

--------------------------------------------------------------------------------
-- Quiver -

-- | quiver of @n@ points and @m@ arrows.
--
-- __Property__ Let @Quiver w o@ be in @'Quiver' __n__ __m__@, then holds:
-- For all @0 '<=' j '<' m@ holds: @s j '<' n@ and @e j '<' n@ where
-- @n = 'lengthN' w@, @s j = 'start' (o j)@ and @e j = 'end' (o j)@.
data Quiver n m = Quiver (Any n) (FinList m (Orientation N))
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- qvOrientaitons -

-- | the orientation of the arrows of a quiver.
qvOrientations :: Quiver n m -> FinList m (Orientation N)
qvOrientations (Quiver _ os) = os

--------------------------------------------------------------------------------
-- Validable -

instance Validable (Quiver n m) where
  valid (Quiver wn os) = vld 0 (lengthN wn) os where
    vld :: N -> N -> FinList m (Orientation N) -> Statement
    vld _ _ Nil = SValid
    vld j n ((s :> e):|os)
      = And [ (s < n) :?> Params ["(j,s,n)":= show (j,s,n)]
            , (e < n) :?> Params ["(j,e,n)":= show (j,e,n)]
            , vld (succ j) n os
            ]

instance (Typeable n, Typeable m) => Entity (Quiver n m)

--------------------------------------------------------------------------------
-- Duality -

type instance Dual (Quiver n m) = Quiver n m

-- | the dual of a quiver, with inverse 'coQuiverInv'.
coQuiver :: Quiver n m -> Dual (Quiver n m)
coQuiver (Quiver wn os) = Quiver wn (amap1 opposite os)

-- | from the dual quiver, with inverse 'coQuiver'.
coQuiverInv :: Dual (Quiver n m) -> Quiver n m
coQuiverInv = coQuiver


