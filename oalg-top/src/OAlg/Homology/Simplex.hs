
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
{-    
    -- * Simplex
    Simplex(..), simplex, (<:), spxEmpty

    -- * Face
  , faces
-}
  ) where

import Data.Foldable 

import OAlg.Prelude

import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
-- Simplex -

-- | simplex as 'Z'-indexed sets of vertices in @__x__@.
--
-- __Property__ Let @s = 'Simplex' n xs@ be in @'Simplex' __x__@, then holds:
--
--  (1) For all @.. x,y ..@ in @xs@ holds: @x < y@.
--
--  (2) @'length' xs '==' n '+' 1@.
data Simplex x = Simplex Z [x] deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- spxDim -

-- | the spxDim of a simplex.
spxDim :: Simplex x -> Z
spxDim (Simplex n _) = n

--------------------------------------------------------------------------------
-- spxSet -

-- | the underlying set of vertieces.
spxSet :: Simplex x -> Set x
spxSet (Simplex _ xs) = Set xs

{-
--------------------------------------------------------------------------------
-- Simplex -

-- | simplex as a finite list of a given length @__l__@ of vertices in a space @__x__@.
--
--  __Note__ We allow also simplices with zero length, i.e. the empty simplex.
newtype Simplex l x = Simplex (FinList l x) deriving (Show,Eq, Ord, Validable, Entity,Foldable)

{-
instance Show x => Show (Simplex l x) where
  show  = show . toList 
-}
--------------------------------------------------------------------------------
-- simplex -

-- | the 'Simplex' of dimension @'Dim' __n__@, starting at the given enumerating value @v@.
--
--  __Example__
--
-- >>> simplex (dim :: Dim N4) (0::N)
-- [0,1,2,3,4]
simplex :: Enum v => Any l -> v -> Simplex (l+1) v
simplex n v = Simplex $ spl n v where
  spl :: Enum v => Any n -> v -> FinList (n+1) v
  spl W0 v = v :| Nil
  spl (SW n) v = v :| spl n (succ v) 

--------------------------------------------------------------------------------
-- spxEmpty -

-- | the empty simplex.
spxEmpty :: Simplex N0 x
spxEmpty = Simplex Nil

--------------------------------------------------------------------------------
-- (<:)

-- | cons of a vertex and a simplex.
(<:) :: x -> Simplex l x -> Simplex (l+1) x
v <: Simplex vs = Simplex (v:|vs)

--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex (l+1) x -> FinList (l+1) (Simplex l x)
faces (Simplex (v:|vs)) = case vs of
  Nil  -> spxEmpty :| Nil
  _:|_ -> Simplex vs :| amap1 (v<:) (faces $ Simplex vs)
-}
