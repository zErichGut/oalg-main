
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
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- prpLatticeDisjunction -

-- | validity of disjunction in a lattice.
prpLatticeDisjunction :: (Lattice a, Show a) => a -> a -> a -> Statement
prpLatticeDisjunction a b c = Label "LatticeDisjunction" :<=>:
  And [ Label "a <<= (a || b)"
          :<=>: (a <<= ab) :?> Params ["a":=show a,"b":=show b]
      , Label "b <<= (a || b)"
          :<=>: (b <<= ab) :?> Params ["a":=show a,"b":=show b]
      , Label "(a <<= z) && (b <<= z) ~> (a || b) <<= z"
        :<=>:     (((a <<= z) && (b <<= z)) :?> Params ["a":=show a,"b":=show b,"z":=show z])
              :=> (ab <<= z) :?> Params ["a":=show a,"b":=show b,"z":=show z]
      ]
  where ab = a || b
        z  = ab || c

--------------------------------------------------------------------------------
-- prpLatticeConjunction -

-- | validity of conjunction in a lattice.
prpLatticeConjunction :: (Lattice a, Show a) => a -> a -> a -> Statement
prpLatticeConjunction a b c = Label "LatticeDisjunction" :<=>:
  And [ Label "(a && b) <<= a"
          :<=>: (ab <<= a) :?> Params ["a":=show a,"b":=show b]
      , Label "(a && b) <<= b"
          :<=>: (ab <<= b) :?> Params ["a":=show a,"b":=show b]
      , Label "(z <<= a) && (z <<= b) ~> z <<= (a && b)"
        :<=>:     (((z <<= a) && (z <<= b)) :?> Params ["a":=show a,"b":=show b,"z":=show z])
              :=> (z <<= ab) :?> Params ["a":=show a,"b":=show b,"z":=show z]
      ]
  where ab = a && b
        z  = ab && c

--------------------------------------------------------------------------------
-- prpLattice -

-- | validity of a lattice.
prpLattice :: (Lattice a,Show a) => X a -> Statement
prpLattice xa = Prp "Lattice" :<=>:
  And [ Forall xaaa
          (\(a,b,c) -> And [ prpLatticeDisjunction a b c
                           , prpLatticeConjunction a b c
                           ]
          )
      ]
  where xaaa = xTupple3 xa xa xa

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

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
-- ssUnion -

ssUnion :: SimplexSet s x -> SimplexSet s x -> SimplexSet s x
ssUnion (SimplexSet zssx) (SimplexSet zssy) = SimplexSet $ uni zssx zssy where
  uni [] zssy = zssy
  uni zssx [] = zssx
  uni ((u,ssx):ussx) ((v,ssy):vssy) = case u `compare` v of
    LT -> (u,ssx) : uni ussx ((v,ssy):vssy)
    EQ -> (u,ssx || ssy) : uni ussx vssy
    GT -> (v,ssy) : uni ((u,ssx):ussx) vssy

--------------------------------------------------------------------------------
-- ssIntersection -

ssIntersection :: SimplexSet s x -> SimplexSet s x -> SimplexSet s x
ssIntersection (SimplexSet zssx) (SimplexSet zssy)
  = SimplexSet $ filter (not . setIsEmpty . snd) $ intr zssx zssy where
  intr ((u,ssx):ussx) ((v,ssy):vssy) = case u `compare` v of
    LT -> intr ussx ((v,ssy):vssy)
    EQ -> (u,ssx && ssy) : intr ussx vssy
    GT -> intr ((u,ssx):ussx) vssy
  intr _ _ = []
--------------------------------------------------------------------------------
-- ssDifference -

ssDifference :: SimplexSet s x -> SimplexSet s x -> SimplexSet s x
ssDifference (SimplexSet zssx) (SimplexSet zssy)
  = SimplexSet $ filter (not . setIsEmpty . snd) $ diff zssx zssy where
  diff [] _    = []
  diff zssx [] = zssx
  diff ((u,ssx):ussx) ((v,ssy):vssy) = case u `compare` v of
    LT -> (u,ssx):diff zssx ((v,ssy):vssy)
    EQ -> (u,ssx // ssy) : diff ussx vssy
    GT -> diff ((u,ssx):ussx) vssy

--------------------------------------------------------------------------------
-- isSubSimplexSet -

isSubSimplexSet :: SimplexSet s x -> SimplexSet s x -> Bool
isSubSimplexSet (SimplexSet zssx) (SimplexSet zssy) = sub zssx zssy where
  sub [] _ = True
  sub _ [] = False
  sub ((u,ssx):ussx) ((v,ssy):vssy) = case u `compare` v of
    LT -> False
    EQ -> (ssx <<= ssy) && sub ussx vssy
    GT -> sub ((u,ssx):ussx) vssy

--------------------------------------------------------------------------------
-- SimplexSet - Lattice -

instance POrd (SimplexSet s x) where
  (<<=) = isSubSimplexSet

instance Logical (SimplexSet s x) where
  (||) = ssUnion
  (&&) = ssIntersection

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

--------------------------------------------------------------------------------
-- X -

-- | random variable of 'SimplexSet' generated by the maximal given number of simplices.
xSimplexSet :: (Simplical s, Entity (s x), Ord (s x)) => N -> X (s x) -> X (SimplexSet s x)
xSimplexSet n xsx = amap1 simplexSet $ xTakeB 0 n xsx

--------------------------------------------------------------------------------
-- prpSimplexSet -

-- | validity of the implementation of 'SimplexSet'
prpSimplexSet :: Statement
prpSimplexSet = Label "SimplexSet" :<=>:
  And [ Label "s ~ Set" :<=>: prpLattice xSimplexSetSet
      , Label "s ~ []" :<=>: prpLattice xSimplexSetLst
      ]
  where
    maxDim = 10
    maxGen = 20
    xv      = xOneOf ['a'..'z']
    
    xSimplexSetSet = xSimplexSet maxGen (xSet (succ maxDim) xv)
    xSimplexSetLst = xSimplexSet maxGen (xTakeB 0 (succ maxDim) xv)
