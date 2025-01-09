
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , DataKinds
  , TupleSections
#-}

-- |
-- Module      : OAlg.Homology.SimplexSet
-- Description : sets of simplices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- sets of simplices..
module OAlg.Homology.SimplexSet
  (
  ) where

import Control.Monad

import Data.Typeable
import Data.List (filter)

import OAlg.Prelude 

import OAlg.Entity.Sequence.Set

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- SimplexSet -

-- | set of simplices over @__x__@ according to @__s__@.
--
-- __Properties__ Let @'SimplexSet' zssx@ be in @'SimplexSet' __s__ __x__@ for a 'Simplical' structure
-- @__s__@, then holds:
--
-- (1) For all @(z,ssx)@ in @zssx@ holds:
--
--    (1) @ssx@ is not empty.
--
--    (2) @'dimension' sx '==' z@ for all @sx@ in @ssx@.
--
-- (2) For all @..(z,ssx):(z',ssx')..@ in @zssx@ holds: @z < z'@.
data SimplexSet s x where
  SimplexSet :: (Entity (s x), Ord (s x)) => [(Z,Set (s x))] -> SimplexSet s x

deriving instance Show (SimplexSet s x)
deriving instance Eq (SimplexSet s x)
deriving instance Ord (SimplexSet s x)

instance (Simplical s, Typeable s, Typeable x) => Validable (SimplexSet s x) where
  valid (SimplexSet zssx) = Label "SimplexSet" :<=>:
    case zssx of
      []            -> SValid
      (z,ssx):zssx' -> And [ vldDimension z ssx
                           , vldSucc z zssx'
                           ]
    where
      vldDimension z ssx = And [ valid z
                               , valid ssx
                               , Label "1.1" :<=>: not (setIsEmpty ssx) :?> Params ["ssx":=show ssx]
                               , Label "1.2" :<=>: let z' = amap1 (EntOrdMap dimension) ssx in
                                   (z' == Set [z]) :?> Params ["z'":=show z']
                               ]

      vldSucc _ [] = SValid
      vldSucc z ((z',ssx'):zssx)
        = And [ vldDimension z' ssx'
              , Label "2" :<=>: (z < z') :?> Params ["z":=show z, "z'":=show z']
              , vldSucc z' zssx
              ]

instance (Simplical s, Typeable s, Typeable x) => Entity (SimplexSet s x)

--------------------------------------------------------------------------------
-- ssxs -

ssxs :: SimplexSet s x -> [(Z,Set (s x))]
ssxs (SimplexSet zssx) = zssx

--------------------------------------------------------------------------------
-- simplexSet -

simplexSet :: (Simplical s, Entity (s x), Ord (s x)) => [s x] -> SimplexSet s x
simplexSet sxs = SimplexSet $ setxs $ spxDimSets sxs

--------------------------------------------------------------------------------
-- ssDifference -

ssDifference :: SimplexSet s x -> SimplexSet s x -> SimplexSet s x
ssDifference (SimplexSet zssx) (SimplexSet zssy)
  = SimplexSet $ filter (not . setIsEmpty . snd) $ diff zssx zssy where
  diff [] _    = []
  diff zssx [] = zssx
  diff ((z,ssx):zssx) ((z',ssy):zssy) = case z `compare` z' of
    LT -> (z,ssx):diff zssx ((z',ssy):zssy)
    EQ -> (z,ssx `setDifference` ssy) : diff zssx zssy
    GT -> diff ((z,ssx):zssx) zssy

--------------------------------------------------------------------------------
-- isSubSimplexSet -

isSubSimplexSet :: SimplexSet s x -> SimplexSet s x -> Bool
isSubSimplexSet = error "nyi"

--------------------------------------------------------------------------------
-- SimplexSet - Lattice -

instance POrd (SimplexSet s x) where
  (<<=) = isSubSimplexSet

instance Logical (SimplexSet s x) where
  (||) = error "nyi"
  (&&) = error "nyi"

instance Lattice (SimplexSet s x)

instance ErasabelLattice (SimplexSet s x) where
  (//) = ssDifference

--------------------------------------------------------------------------------
-- ssFilterSimpliex -

ssFilterSimplex :: (s x -> Bool) -> SimplexSet s x -> SimplexSet s x
ssFilterSimplex p (SimplexSet zssx)
  = SimplexSet $ filter (not . setIsEmpty . snd) $ amap1 (\(z,ssx) -> (z,setFilter p ssx)) zssx 

--------------------------------------------------------------------------------
-- ssFilterVertex -

ssFilterVertex :: (x -> Bool) -> SimplexSet Set x -> SimplexSet Set x
ssFilterVertex p (SimplexSet zssx)
  = simplexSet
  $ amap1 (setFilter p)
  $ join
  $ amap1 (setxs . snd) zssx

--------------------------------------------------------------------------------
-- ssDimSimplices -

ssDimSimplices :: SimplexSet s x -> Set (Z,s x)
ssDimSimplices (SimplexSet zssx)
  = Set
  $ join
  $ amap1 (adjDim . (\(z,ssx) -> (z,setxs ssx)))
  $ zssx
  where adjDim :: (Z,[x]) -> [(Z,x)]
        adjDim (z,xs) = amap1 (z,) xs
  
--------------------------------------------------------------------------------
-- ssIndex -

ssIndex :: SimplexSet s x -> (Z,s x) -> Maybe N
ssIndex ss@(SimplexSet _) = setIndex $ ssDimSimplices ss

--------------------------------------------------------------------------------
-- ssElem -

ssElem :: Simplical s => SimplexSet s x -> s x -> Bool
ssElem = elem . ssIndex where
  elem :: Simplical s => ((Z,s x) -> Maybe N) -> s x -> Bool
  elem f = isJust . f . spxAdjDim

--------------------------------------------------------------------------------
-- ssMap -

ssMap :: Simplical s => EntOrdMap x y -> SimplexSet s x -> SimplexSet s y
ssMap f s = case structEntOrd f s of
  Struct -> simplexSet $ amap1 (amap1 f) $ join $ amap1 (setxs . snd) $ ssxs s
  where
    structEntOrd :: Simplical s => EntOrdMap x y -> SimplexSet s x -> Struct EntOrd (s y)
    structEntOrd (EntOrdMap _) _ = tau1 Struct

--------------------------------------------------------------------------------
-- SimplexSet - Functorial1 -

instance Simplical s => Applicative1 EntOrdMap (SimplexSet s) where amap1 = ssMap
instance Simplical s => Functorial1 EntOrdMap (SimplexSet s)

--------------------------------------------------------------------------------

ss :: N -> N -> SimplexSet [] N
ss d n = SimplexSet $ takeN (succ d) $ simplices $ Set [1..n]

