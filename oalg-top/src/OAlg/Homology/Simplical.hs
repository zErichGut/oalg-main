
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , GADTs
           , TupleSections
           , DefaultSignatures
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

    -- * Homological
  , Homological

    -- * Asc
  , Asc(..), ascxs, asc

    -----------------------------------------
  , EntOrdMap(..)

    
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

import Data.List (head,tail,filter,sort,groupBy,(++),zip)
import Data.Foldable

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Entity.Sequence.Set

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- spxCombinations -

spxCombinations :: Set x -> [(Z,Set [x])]
spxCombinations (Set vs) = cbns (-1) [[]] where
  -- cbns :: Z -> [x] -> [[x]] -> [(N,[[x]])]
  cbns n xss = (n,Set xss) : cbns (succ n) [v:xs | v <- vs, xs <- xss]

--------------------------------------------------------------------------------
-- EntOrdMap -

-- | mapping between orderd entity types.
data EntOrdMap x y where
  EntOrdMap :: (Entity x, Ord x, Entity y, Ord y) => (x -> y) -> EntOrdMap x y

instance Morphism EntOrdMap where
  type ObjectClass EntOrdMap = EntOrd
  homomorphous (EntOrdMap _) = Struct :>: Struct

instance Category EntOrdMap where
  cOne Struct = EntOrdMap id
  EntOrdMap f . EntOrdMap g = EntOrdMap (f.g)

instance Applicative1 EntOrdMap [] where
  amap1 (EntOrdMap f) xs = amap1 f xs

instance Functorial1 EntOrdMap []

instance Applicative1 EntOrdMap Set where
  amap1 (EntOrdMap f) (Set xs) = set $ amap1 f xs

instance Functorial1 EntOrdMap Set

instance Transformable1 Set EntOrd where
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
--  __Properties__ Let @__s__@ be a type instance of the class 'Simplical', then holds:
--
-- (1) For all @__x__@ and @s@ in @__s__ __x__@ holds:
-- @'dimension' s' '==' 'dimension' s '-' 1@ for all @s'@ in @'faces' s@.
--
-- (2) For all @sx@ in @'Set' __x__@ and @..(_,ssu)':'(_,ssv)..@ in @'simplices' sx@ holds:
-- @'faces'' ssv '==' ssu@.
--
-- (3) For all @f@ in @'EntOrdMap' __x__ __y__@ and @sx@ in @__s__ __x__@ holds:
-- @'vertices' ('amap1' f sx) '==' 'amap1' f ('vertices' sx)@.
class (Functorial1 EntOrdMap s, Transformable1 s EntOrd)  => Simplical s where
  -- | the dimension of a simplex
  dimension :: s x -> Z
  -- | the empty simplex.
  vertices :: Ord x => s x -> Set x
  -- | the face of a simplex.
  faces :: s x -> [s x]
  -- | all simplices for the given set of vertices, starting with 'dimension' @-1@.
  simplices :: Set x -> [(Z,Set (s x))] 

--------------------------------------------------------------------------------
-- vertex -

vertex :: x -> Set x
vertex x = Set [x]

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
spxDimSets :: (Simplical s, Ord (s x)) => [s x] -> Set ((Z,Set (s x)))
spxDimSets = Set . amap1 dsets . groupBy (~) . sort . amap1 spxAdjDim  where
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
-- Homological -

-- | simplical structures, where the application of a 'EntOrdMap' preserves the 'dimension' of the
-- simplices.
--
-- __Property__ Let @__s__@ be a instance of 'Homological', then holds:
-- For each @f@ in @'EntOrdMap' __x__ __y__@ and @s@ in @__s__ __x__@ holds:
-- @'dimension' ('amap1' f s) '==' 'dimension' s@.
class Simplical s => Homological s

--------------------------------------------------------------------------------
-- [] - Simplical -

instance Simplical [] where
  dimension    = pred . inj . lengthN
  vertices     = set
  faces []     = []
  faces (x:xs) = xs : amap1 (x:) (faces xs)
  simplices    = spxCombinations

instance Homological []

--------------------------------------------------------------------------------
-- Set - Simplical -

instance Simplical Set where
  dimension (Set xs) = dimension xs
  vertices           = id
  faces (Set xs)     = amap1 Set $ faces xs
  simplices          = subsets
  
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

instance Applicative1 EntOrdMap Asc where
  amap1 (EntOrdMap f) (Asc xs) = Asc $ sort $ amap1 f xs

instance Functorial1 EntOrdMap Asc

instance Transformable1 Asc Ord' where tau1 Struct = Struct
instance Transformable1 Asc EntOrd where tau1 Struct = Struct

instance Simplical Asc where
  dimension (Asc xs) = dimension xs
  vertices (Asc xs)  = set xs
  faces (Asc xs)     = amap1 Asc $ faces xs
  simplices          = ascCombinations

instance Homological Asc
