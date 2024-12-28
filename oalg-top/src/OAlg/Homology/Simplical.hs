
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
-- Module      : OAlg.Homology.Simplical
-- Description : simplices and there faces.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Simplices and there faces.
module OAlg.Homology.Simplical
  (
    -- * Simplical
    Simplical(..), faces', spxDimSets
  , spxAdjDim, spxFilter
  , vertex

    -- * Asc
  , Asc(..), ascxs, asc

    -----------------------------------------
  , OrdMap(..), subsets
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

import Data.List (head,tail,filter,sort,group,groupBy,(++),reverse,zip)
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
-- spxCombinations -

spxCombinations :: Set x -> [(Z,Set [x])]
spxCombinations (Set vs) = cbns (-1) [[]] where
  -- cbns :: Z -> [x] -> [[x]] -> [(N,[[x]])]
  cbns n xss = (n,Set xss) : cbns (succ n) [v:xs | v <- vs, xs <- xss]

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

subsets :: Set x -> [(Z,Set (Set x))]
subsets (Set []) = [(-1,Set [Set []])]
subsets (Set (x:xs)) = (-1,Set [Set []]) : (x <<: subsets (Set xs)) where
  (<<:) :: x -> [(Z,Set (Set x))] -> [(Z,Set (Set x))]
  x <<: ((_,Set ss):(n,Set ss'):nss) = (n,Set (amap1 (x<:) ss ++ ss')) : (x <<: ((n,Set ss'):nss))
  x <<: [(n,Set ss)]                 = [(succ n,Set $ amap1 (x<:) ss)]
  _ <<: []                           = throw $ ImplementationError "subsets"

  x <: Set xs = Set (x:xs)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Simplical -

-- | abstract simplices over @__x__@. We will call an element of @__s__ __x__@ a
--  __/simplex/__ over @__x__@.
--
--  __Properties__ Let @__s__@ be a type instance of the class 'Simplical' and @s@ in @__s__ __x__@,
-- then holds: @'dimension' f '==' 'dimension' s '-' 1@ for  all @f@ in @'faces' s@.
class Simplical s where
  -- | the dimension of a simplex
  dimension :: s x -> Z
  -- | the underlying set of vertices.
  vertices  :: Ord x => s x -> Set x
  -- | the face of a simplex.
  faces     :: s x -> [s x]

--------------------------------------------------------------------------------
-- vertex -

vertex :: x -> Set x
vertex x = Set [x]

{-
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
-}
--------------------------------------------------------------------------------
-- faces' -

-- | the faces as set of simplices.
faces' :: (Simplical s, Ord (s x)) => Set (s x) -> Set (s x)
faces' = set . join . amap1 faces . setxs

--------------------------------------------------------------------------------
-- spxAdjDim -

-- | adjoins the dimension to the given simplex.
spxAdjDim :: Simplical s => s x -> (Z,s x)
spxAdjDim s = (dimension s,s)

--------------------------------------------------------------------------------
-- spxDimSets -

-- | the grouped simplices according to there dimension with increasing dimension.
spxDimSets :: (Simplical s, Ord (s x)) => [s x] -> [(Z,Set (s x))]
spxDimSets ss = amap1 dsets $ groupBy (~) $ sort $ amap1 spxAdjDim ss where

  (d,_) ~ (d',_) = d == d'
    
  dsets :: [(z,s)] -> (z,Set s)
  dsets zss = (d zss,Set $ amap1 snd zss) where d = fst . head

--------------------------------------------------------------------------------
-- spxFilter

-- | filtering of a simplex list according the given predicate.
spxFilter :: ((Z,s) -> Bool) -> [(Z,Set s)] -> [(Z,Set s)]
spxFilter p = amap1 (setFilter p) where
  setFilter :: ((Z,s) -> Bool) -> (Z,Set s) -> (Z,Set s)
  setFilter p (z,Set ss) = (z,Set $ filter (\s -> p (z,s)) ss)

--------------------------------------------------------------------------------
-- [] - Simplical -

instance Simplical [] where
  dimension    = pred . inj . lengthN
  vertices     = set
  faces []     = []
  faces (x:xs) = xs : amap1 (x:) (faces xs)

--------------------------------------------------------------------------------
-- Set - Simplical -

instance Simplical Set where
  dimension (Set xs) = dimension xs
  vertices           = id
  faces (Set xs)     = amap1 Set $ faces xs
  
--------------------------------------------------------------------------------
-- Asc -

-- | ascending list with elements in @__x__@.
--
-- __Property__ Let @'Asc' xs@ be in @'Asc' __x__@, then holds:
-- For all @..x':'y..@ in @xs@ holds: @x '<=' y@.
newtype Asc x = Asc [x] deriving (Show,Eq,Ord,Foldable,LengthN)

instance (Validable x, Ord x, Show x) => Validable (Asc x) where
  valid (Asc xs) = Label "Asc" :<=>: case xs of
    []    -> SValid
    x:xs' -> valid x && vldAsc (0::N) x xs'
    where
      vldAsc _ _ []     = SValid
      vldAsc i x (y:xs) = And [ valid y
                              , (x <= y) :?> Params ["i":=show i, "x":=show x, "y":=show y]
                              , vldAsc (succ i) y xs
                              ]

instance (Entity x, Ord x) => Entity (Asc x)

--------------------------------------------------------------------------------
-- ascxs -

ascxs :: Asc x -> [x]
ascxs (Asc xs) = xs

--------------------------------------------------------------------------------
-- asc -

asc :: Ord x => [x] -> Asc x
asc = Asc . sort

--------------------------------------------------------------------------------
-- ascCombinations -

ascCombinations :: Set x -> [(Z,Set (Asc x))]
ascCombinations (Set xs) = cbs xs where
  cbs []     = (-1,Set [Asc []]) : es 0
  cbs (x:xs) = (-1,Set [Asc []]) : amap1 (uncurry (<+>)) (adj x cbs' `zip` tail cbs') where
    cbs' = cbs xs

  es z = (z,Set []): es (succ z) 

  (<+>) :: (Z,Set (Asc x)) -> (Z,Set (Asc x)) -> (Z,Set (Asc x))
  (z,Set as) <+> (_,Set bs) = (z,Set (as ++ bs))
  
  
  -- adjoins 1 to n x to the sequence
  adj :: x -> [(Z,Set (Asc x))] -> [(Z,Set (Asc x))] 
  adj x zs = head zs' : amap1 (uncurry (<+>)) (adj x zs' `zip` tail zs' ) where
    zs'  = amap1 (\(z,s) -> (succ z, x <+ s)) zs
  
    (<+) :: x -> Set (Asc x) -> Set (Asc x)
    x <+ Set as = Set $ amap1 (x<:) as
  
    (<:) :: x -> Asc x -> Asc x
    x <: Asc xs = Asc (x:xs)

--------------------------------------------------------------------------------
-- Asc - Simplical -

instance Applicative1 OrdMap Asc where
  amap1 (OrdMap f) (Asc xs) = Asc $ sort $ amap1 f xs

instance Functorial1 OrdMap Asc

instance Transformable1 Asc Ord' where tau1 Struct = Struct

instance Simplical Asc where
  dimension (Asc xs) = dimension xs
  vertices (Asc xs)  = set xs
  faces (Asc xs)     = amap1 Asc $ faces xs
