
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
    Simplex(..), spxDim, spxxs, spxEmpty, spxMap

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
newtype Simplex x = Simplex [x] deriving (Show,Eq,Foldable,Validable,Entity)

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
-- spxxs -

-- | the underlying set of vertices.
spxxs :: Simplex x -> [x]
spxxs (Simplex xs) = xs

--------------------------------------------------------------------------------
-- spxEmpty -

-- | the empty simplex.
spxEmpty :: Simplex x
spxEmpty = Simplex []

--------------------------------------------------------------------------------
-- spxMap -

spxMap :: (x -> y) -> Simplex x -> Simplex y
spxMap f (Simplex xs) = Simplex $ amap1 f xs

--------------------------------------------------------------------------------
-- (<:) -
infixr 5 <:
  
(<:) :: x -> Simplex x -> Simplex x
x <: Simplex xs = Simplex (x:xs)
  
--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex x -> [Simplex x]
faces (Simplex [])     = []
faces (Simplex (x:xs)) = Simplex xs : amap1 (x<:) (faces $ Simplex xs) where


--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: Ord x => Set (Simplex x) -> Set (Simplex x)
faces' = set . join . amap1 faces . setxs
    

