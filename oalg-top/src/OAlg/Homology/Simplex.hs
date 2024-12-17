
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , GADTs
           , TupleSections
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
    -- * Simplical
    Simplical(..), faces'

  , subsets
{-    
    -- * Simplex
    Simplex(..), simplex, spxDim, spxxs, spxEmpty, spxMap

    -- * Face
  , faces, faces'

    -- * Propostion
  , prpSimplex
-}
  ) where

import Control.Monad (join)

import Data.List (head,filter,sort,group,groupBy,(++),reverse)
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Entity.Sequence.Set

import OAlg.Structure.Additive

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Functorial1 -

-- | representable categories, i.e. covariant functors from an 'Applicative1' category @__c__@ to
-- @('->')@.
--
-- __Properties__ Let the pair @(__c__,__f__)@ be a type instance of 'Functorial1', then holds:
--
-- (1) For all types @__x___@ and @d@ in @'Struct' ('ObjectClass' __c__) __x__@ holds:
-- @'amap1' ('cOne' d) = 'id'@.
--
-- (2) For all types @__x__@, @__y__@, @__z__@, @f@ in @__c__ __y__ __z__@ and
-- @g@ in @__c__ __x__ __y__@ holds: @'amap1' (f '.' g) = 'amap1' f '.' 'amap1' g@.
class (Category c, Applicative1 c f) => Functorial1 c f 

--------------------------------------------------------------------------------
-- combinations -

combinations :: N -> [x] -> [[x]]
combinations n xs = cbns n xs [[]] where
  cbns 0 _ xss  = xss
  cbns n xs xss = cbns (pred n) xs [x:cbs | x <- xs, cbs <- xss] 

--------------------------------------------------------------------------------
-- OrdMap -

-- | mapping between orderd types.
data OrdMap x y where
  OrdMap :: (Ord x, Ord y) => (x -> y) -> OrdMap x y

instance Morphism OrdMap where
  type ObjectClass OrdMap = Ord'
  homomorphous (OrdMap _) = Struct :>: Struct

instance Category OrdMap where
  cOne Struct = OrdMap id
  OrdMap f . OrdMap g = OrdMap (f.g)

instance Applicative1 OrdMap [] where
  amap1 (OrdMap f) xs = amap1 f xs

instance Functorial1 OrdMap []

instance Transformable1 [] Ord' where
  tau1 Struct = Struct

instance Applicative1 OrdMap Set where
  amap1 (OrdMap f) (Set xs) = set $ amap1 f xs

instance Functorial1 OrdMap Set

instance Transformable1 Set Ord' where
  tau1 Struct = Struct
  
--------------------------------------------------------------------------------
-- subsets -

-- | the list of subsets of given set.
subsets :: Ord x => Set x -> [Set x]
subsets (Set [])     = [Set []]
subsets (Set (x:xs)) = amap1 (x<:) ss ++ ss where
  ss = subsets (Set xs)
  x <: Set xs = Set (x:xs)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Simplical -

-- | abstract simplex over @__x__@.
--
--  __Properties__ Let @__s__@ be a type instance of the class 'Simplical' and @__x__@ a type
-- instance of 'Ord', then holds:
--
-- (1) For all @s@ in @__s__ __x__@ holds: @-1 '<=' 'dimension' s@.
--
-- (2) @'dimension' ('spxEmpty' :: __s__ __x__) '==' -1@.
--
-- (3) For all @v@ in @__x__@ holds: @'dimension' ('vertex' v) '==' 0@.
--
-- (4) For all @s@ in @__s__ __x__@ holds:
--
--    (1) @'dimension' f '==' 'dimension' s '-' 1@ for
--        all @f@ in @'faces' s@.
--
--    (2) If @'dimension' s '==' 0@ then holds: @'faces' s '==' ['spxEmpty']@.
--
-- (5) For all @s@ in @__s__ __x__@ holds: @'simplex' ('toList' s) '==' s@. 
--
-- (6) For all @__y__@, @f@ in @'OrdMap' __x__ __y__@ and @xs@ in @[__x__]@ holds:
-- @ 'amap1' f ('simplex' xs) '==' 'simplex' ('amap1' f xs)@.
class (Functorial1 OrdMap s, Foldable s, Transformable1 s Ord') => Simplical s where
  dimension :: s x -> Z
  simplex   :: Ord x => [x] -> s x
  faces     :: s x -> [s x]

--------------------------------------------------------------------------------
-- spxEmpty -

-- | the empty simplex.
spxEmpty :: (Simplical s, Ord x) => s x
spxEmpty = simplex []

--------------------------------------------------------------------------------
-- vertex -

vertex :: (Simplical s, Ord x) => x -> s x
vertex x = simplex [x]

--------------------------------------------------------------------------------
-- spxOrd -

-- | infering the 'Ord'-structure,
spxOrd :: (Simplical s, Ord x) => f (s x) -> Struct Ord' (s x)
spxOrd _ = tau1 Struct

--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: (Simplical s, Ord x) => Set (s x) -> Set (s x)
faces' ss = case spxOrd ss of Struct -> set $ join $ amap1 faces $ setxs ss

--------------------------------------------------------------------------------
-- spxAdjDim -

-- | adjoins the dimension to the given simplex.
spxAdjDim :: Simplical s => s x -> (Z,s x)
spxAdjDim s = (dimension s,s)

--------------------------------------------------------------------------------
-- spxDimSets -

-- | the grouped simplices according to there dimension with increasing dimension.
spxDimSets :: (Simplical s, Ord x) => [s x] -> [(Z,Set (s x))]
spxDimSets ss = case spxOrd ss of Struct -> amap1 dsets $ groupBy (~) $ sort $ amap1 spxAdjDim ss
  where

    (d,_) ~ (d',_) = d == d'
    
    dsets :: [(z,s)] -> (z,Set s)
    dsets zss = (d zss,Set $ amap1 snd zss) where d = fst . head

--------------------------------------------------------------------------------
-- [] - Simplical -

instance Simplical [] where
  dimension = pred . inj . lengthN
  simplex      = id
  faces []     = []
  faces (x:xs) = xs : amap1 (x:) (faces xs) where

--------------------------------------------------------------------------------
-- Set - Simplical -

instance Simplical Set where
  dimension s    = pred $ inj $ lengthN s
  simplex        = set
  faces (Set xs) = amap1 Set $ faces xs

{-
--------------------------------------------------------------------------------
-- <*> -

(<*>) :: (Ord x, Ord y) => Set x -> Set y -> [Set (x,y)]
Set [] <*> _ = []
_ <*> Set [] = []
xs <*> ys    = setxs $ subsets d $ Set [(x,y) | x <- setxs xs, y <- setxs ys] where
  d = prj (dimension xs + dimension ys + 1)
-}











{-
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


-}

