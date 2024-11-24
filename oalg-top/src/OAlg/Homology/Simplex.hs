
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , GeneralizedNewtypeDeriving
           , DataKinds
#-}

-- |
-- Module      : OAlg.Homology.Simplex
-- Description : simplices and there faces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Simplices and there faces.
module OAlg.Homology.Simplex
  (
    -- * Simplex
    Simplex(..), simplex, spxDim, spxSet, spxEmpty

    -- * Face
  , faces, faces'
  ) where

import Control.Monad (join)

import Data.Foldable 

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
-- Simplex -

-- | simplex as a set of vertices in @__x__@.
--
-- __Note__ The ordering of simplices is adapted to comparing first there length, e.g.
-- @'simplex' "b" '<=' 'simplex' "ab"@ is 'True'.
newtype Simplex x = Simplex (Set x) deriving (Show,Eq,Foldable,Validable,Entity)

--------------------------------------------------------------------------------
-- Simplex - Ord -

instance Ord x => Ord (Simplex x) where
  compare (Simplex xs) (Simplex ys) = compare (length xs,xs) (length ys,ys)

--------------------------------------------------------------------------------
-- Simplex - LengthN -

instance LengthN (Simplex x) where
  lengthN (Simplex xs) = lengthN xs
  
--------------------------------------------------------------------------------
-- spxDim -

-- | the dimension of a simplex.
spxDim :: Simplex x -> Z
spxDim (Simplex xs) = pred $ inj $ length xs

--------------------------------------------------------------------------------
-- spxSet -

-- | the underlying set of vertices.
spxSet :: Simplex x -> Set x
spxSet (Simplex xs) = xs

--------------------------------------------------------------------------------
-- spxEmpty -

-- | the empty simplex.
spxEmpty :: Simplex x
spxEmpty = Simplex (Set [])

--------------------------------------------------------------------------------
-- simplex -

-- | the induced simplex.
simplex :: Ord x => [x] -> Simplex x
simplex = Simplex . set

--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex x -> [Simplex x]
faces (Simplex (Set []))     = []
faces (Simplex (Set (x:xs))) = Simplex (Set xs) : amap1 (x<:) (faces $ Simplex $ Set xs) where
  x <: Simplex (Set xs) = Simplex (Set (x:xs))

--------------------------------------------------------------------------------
-- faces' -

-- | the faces of as set of simplices.
faces' :: Ord x => Set (Simplex x) -> Set (Simplex x)
faces' = set . join . amap1 faces . setxs
    
