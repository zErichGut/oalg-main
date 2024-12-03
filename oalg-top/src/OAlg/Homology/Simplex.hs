
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
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
    Simplex(..), simplex, spxDim, spxxs, spxEmpty, spxMap

    -- * Face
  , faces, faces'

    -- * Propostion
  , prpSimplex

  ) where

import Control.Monad (join)

import Data.Foldable 

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Symbol

import OAlg.Structure.Operational

import OAlg.Entity.Sequence

--------------------------------------------------------------------------------
-- Simplex -

-- | simplex as a increasing list of vertices in @__x__@.
--
--  __Property__ Let @'Simplex' [v 0, v 1 .. v n]@ be in @'Simplex' __x__@, then holds:
--  @v i '<=' v (i+1)@ for @i = 0..n-1@,
--
-- __Note__ The ordering of simplices is adapted by comparing first there length, e.g.
-- @'simplex' "b" '<=' 'simplex' "ab"@ is 'True'.
newtype Simplex x = Simplex [x] deriving (Show,Eq,Foldable,Entity)

instance (Ord x, Validable x, Show x) => Validable (Simplex x) where
  valid (Simplex [])     = SValid
  valid (Simplex (v:vs)) = valid v && vldInc v vs where
    vldInc _ []     = SValid
    vldInc v (w:vs) = And [ valid w
                          , Label "inc" :<=>:
                              (v <= w) :?> Params ["v":=show v,"w":=show w]
                          , vldInc w vs
                          ] 
                              
--------------------------------------------------------------------------------
-- Simplex - Ord -

instance Ord x => Ord (Simplex x) where
  compare (Simplex xs) (Simplex ys) = compare (length xs,xs) (length ys,ys)

--------------------------------------------------------------------------------
-- Simplex - LengthN -

instance LengthN (Simplex x) where
  lengthN (Simplex xs) = lengthN xs

--------------------------------------------------------------------------------
-- simplex -

-- | the induced simplex together with its permutation to sort it.
--
--  __Property__ Let @xs@ be in @[__x__]@ and @'Simplex' xs',p) = 'simplex' xs@, then holds:
--  @xs '<*' p '==' xs'@. 
simplex :: (Entity x, Ord x) => [x] -> (Simplex x,Permutation N)
simplex xs = (Simplex xs',p) where
  (xs',p) = permuteByN compare id xs

--------------------------------------------------------------------------------
-- prpSimplex -

-- | validity of 'simplex'.
prpSimplex :: N -> Statement
prpSimplex n = Prp "Simplex" :<=>: Forall (xs n) vldSpx where
  xs :: N -> X [Symbol]
  xs n = do
    n' <- xNB 0 n
    xTakeN n' xStandard

  vldSpx xs = valid s && (xs <* p == spxxs s) :?> Params ["xs":=show xs] where
    (s,p) = simplex xs 
  
--------------------------------------------------------------------------------
-- spxDim -

-- | the dimension of a simplex.
spxDim :: Simplex x -> Z
spxDim (Simplex xs) = pred $ inj $ length xs

--------------------------------------------------------------------------------
-- spxxs -

-- | the underlying increasing list of vertices.
spxxs :: Simplex x -> [x]
spxxs (Simplex xs) = xs

--------------------------------------------------------------------------------
-- spxEmpty -

-- | the empty simplex.
spxEmpty :: Simplex x
spxEmpty = Simplex []


--------------------------------------------------------------------------------
-- spxMap -

-- | maps the given simplex according to the mapping function.
spxMap :: (Entity y, Ord y) => (x -> y) -> Simplex x -> (Simplex y, Permutation N)
spxMap f (Simplex xs) = simplex $ amap1 f xs


--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex x -> [Simplex x]
faces (Simplex [])     = []
faces (Simplex (x:xs)) = Simplex xs : amap1 (x<:) (faces $ Simplex xs) where
    x <: Simplex xs = Simplex (x:xs)


--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: Ord x => Set (Simplex x) -> Set (Simplex x)
faces' = set . join . amap1 faces . setxs


