
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , GeneralizedNewtypeDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.ComplexSimplical
-- Description : complexes of simplical sets over a complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- complexes of simplical sets over a complex.
module OAlg.Homology.ComplexSimplical
  (
  ) where

import Data.Typeable

import Data.List as L (zip,(++),repeat,filter)

import OAlg.Prelude

-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

-- import OAlg.Hom.Fibred
-- import OAlg.Hom.Additive
-- import OAlg.Hom.Vectorial

import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
-- import OAlg.Entity.Sequence.Graph
-- import OAlg.Entity.Sum
import OAlg.Entity.Matrix

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.Chain


--------------------------------------------------------------------------------
-- ComplexSimplical -

-- | complexe of simplical sets over a given complex.
--
-- __Properties__ Let @'ComplexSimplical' c zssx@ be in @'ComplexSimplical' __s__ __n__ __x__@, then
-- holds:
--
-- (1) @z0 '==' -1@ where @(z0,_) = 'head' zssx@.
--
-- (2) For all @(z,'Set' sxs)@ in @zssx@ and @sx@ in @sxs@ holds:
--
--     (1) @'dimension' sx '==' z@
--
--     (2) @'verteices' sx@ is an element of @c@.
--
-- (3) For all @..(z,su)':'(z',sv)..@ in @zsx@ holds:
--
--    (1) @z' '==' z '+' 1@.
--
--    (2) @'faces'' sv'@ is a subset of @su@.
data ComplexSimplical s n x
  = ComplexSimplical (Complex x) (FinList (n+3) (Z,Set (s x)))
  deriving (Show,Eq,Ord)

instance (Simplical s, Entity (s x), Ord (s x), Entity x, Ord x)
  => Validable (ComplexSimplical s n x) where
  valid (ComplexSimplical c zssx) = Label "ComplexSimplical" :<=>:
    And [ valid c
        , valid sxs0
        , Label "1" :<=>: (z0 == -1) :?> Params ["z0":=show z0]
        , vldDimensionVertices elg z0 sxs0
        , vldFacesVertices elg z0 sxs0 (F.tail zssx)
        ]
    where
      (z0,sxs0) = F.head zssx
      
      elg = setIndex $ cpxSet c

      elem elg sx = case elg (spxAdjDim sx) of
        Nothing -> False
        Just _  -> True

      vldDimensionVertices _ _ (Set []) = SValid
      vldDimensionVertices elg z (Set (sx:sxs))
        = And [ Label "2.1" :<=>: (dimension sx == z) :?> Params ["z":=show z,"sx":=show sx]
              , Label "2,2" :<=>: elem elg (vertices sx) :?> Params ["sx":= show sx]
              , vldDimensionVertices elg z (Set sxs)
              ]

      vldFacesVertices
        :: (Simplical s, Entity (s x), Ord (s x), Ord x)
        => ((Z,Set x) -> Maybe N) -> Z -> Set (s x) -> FinList n (Z,Set (s x)) -> Statement
      vldFacesVertices _ _ _ Nil = SValid
      vldFacesVertices elg z su ((z',sv):|zssx)
        = And [ valid sv
              , Label "3.1" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , vldDimensionVertices elg z' sv
              , Label "3.2" :<=>: let fsv = faces' sv in
                  (fsv `isSubSet` su) :?> Params ["fsv":= show (fsv `setDifference` su)]
              , vldFacesVertices elg z' sv zssx
              ]
    
instance ( Simplical s, Typeable s, Entity (s x), Ord (s x), Entity x, Ord x, Typeable n)
  => Entity (ComplexSimplical s n x)

--------------------------------------------------------------------------------
-- cpxsxs -

cpxsxs :: ComplexSimplical s n x -> FinList (n+3) (Z,Set (s x))
cpxsxs (ComplexSimplical _ zssx) = zssx

--------------------------------------------------------------------------------
-- toFinList3 -

-- | maps a infinite list to a finite list of @__n__ + 3@.
toFinList3 :: Any n -> [x] -> FinList (n+3) x
toFinList3 W0 (x:x':x'':_) = x:|x':|x'':|Nil
toFinList3 (SW n) (x:xs)   = x :| toFinList3 n xs
toFinList3 _ _             = throw $ ImplementationError "toFinList3"

--------------------------------------------------------------------------------
-- simplicalComplex -

-- | the embedding of a complex into a simplical complex.
simplicalComplex :: Any n -> Complex x -> ComplexSimplical Set n x
simplicalComplex n c@(Complex zssx)
  = ComplexSimplical c (toFinList3 n ([-1..] `L.zip` ssx))
  where ssx = amap1 snd zssx L.++ L.repeat setEmpty

--------------------------------------------------------------------------------
-- singularComplex -

-- | complex of simplical sets of the given complex, containing maybe singular simplices.
--
-- __Note__
-- (1) The cardinality of the simplical sets __explodes__ for example @__s__ = []@.
--
-- (2) The result of 'singularComplex' for @__s__ = 'Set'@ and 'simplicalComplex' are equal,
-- but 'simplicalComplex' is faster.
singularComplex :: (Simplical s, Ord x) => Any n -> Complex x -> ComplexSimplical s n x
singularComplex n c = ComplexSimplical c (toFinList3 n ([-1..] `L.zip` ssx)) where
  ssx = amap1 (fl (cpxIndex c)) ((amap1 snd $ simplices $ cpxVertexSet c) L.++ L.repeat setEmpty)

  elem :: (Simplical s, Ord x) => ((Z,Set x) -> Maybe N) -> s x -> Bool
  elem elg sx = case elg $ spxAdjDim $ vertices sx of
    Nothing -> False
    Just _  -> True

  fl :: (Simplical s, Ord x) => ((Z, Set x) -> Maybe N) -> Set (s x) -> Set (s x)
  fl elg (Set sxs) = Set $ filter (elem elg) sxs

scpxl :: Any n -> N -> ComplexSimplical [] n N
scpxl n m = singularComplex n (complex [Set [1..m]])

scpxa :: Any n -> N -> ComplexSimplical Asc n N
scpxa n m = singularComplex n (complex [Set [1..m]])

scpxs :: Any n -> N -> ComplexSimplical Set n N
scpxs n m = singularComplex n (complex [Set [1..m]])

scpxs' :: Any n -> N -> ComplexSimplical Set n N
scpxs' n m = simplicalComplex n (complex [Set [1..m]])

--------------------------------------------------------------------------------
-- cpxsBoundaryRep -

cpxsBoundaryRep :: (Ring r, Commutative r, Simplical s, Typeable s, Entity (s x), Ord (s x))
  => ComplexSimplical s n x
  -> FinList (n+2) (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
cpxsBoundaryRep c = repBoundary (amap1 snd $ cpxsxs c) where
  repBoundary :: (Ring r, Commutative r, Simplical s, Typeable s, Entity (s x), Ord (s x))
    => FinList (n+1) (Set (s x))
    -> FinList n (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
  repBoundary (_:|Nil)       = Nil
  repBoundary (sx:|sx':|sxs) = chainHomRep (Boundary sx' sx) :| repBoundary (sx':|sxs)

cpxsBoundaryRepZ :: (r ~ Z, Simplical s, Typeable s, Entity (s x), Ord (s x))
  => ComplexSimplical s n x
  -> FinList (n+2) (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
cpxsBoundaryRepZ = cpxsBoundaryRep

--------------------------------------------------------------------------------
-- ComplexSimplicalMap -

-- | mapping between complex of simplices, where the underlying map induces a mapping between the two
-- given simplex sets.
--
-- __Property__ Let @'ComplexSimplicalMap' csx csy f@ be in
-- @'ComplexSimplicalMap' __s__ __n__ (ComplexSimplical __s__ __n__ __x__) (ComplexSimplical __s__ __n__ __y__)@
-- then holds for all simplices @s@ in @csx@:
-- @'amap1' f s@ is an element of @csy@.
--
-- __Note__ Because of the property (3) for 'Simplical'-structures it is sufficient that the induced
-- complex map - given by 'cpxsComplexMap' - is 'valid'. 
data ComplexSimplicalMap s n x y where
  ComplexSimplicalMap
    :: ComplexSimplical s n x -> ComplexSimplical s n y
    -> OrdMap x y
    -> ComplexSimplicalMap s n (ComplexSimplical s n x) (ComplexSimplical s n y)

--------------------------------------------------------------------------------
-- cpxsComplexMap -

cpxsComplexMap :: ComplexSimplicalMap s n (ComplexSimplical s n x) (ComplexSimplical s n y)
  -> ComplexMap (Complex x) (Complex y)
cpxsComplexMap (ComplexSimplicalMap (ComplexSimplical cx _) (ComplexSimplical cy _) f)
  = ComplexMap cx cy f

--------------------------------------------------------------------------------
-- ComplexSimplicalMap - Entity -

instance (Simplical s, Entity (s x), Ord (s x), Entity (s y), Ord (s y), Entity x, Entity y)
  => Validable (ComplexSimplicalMap s n (ComplexSimplical s n x) (ComplexSimplical s n y)) where
  valid f@(ComplexSimplicalMap csx csy (OrdMap _)) = Label "ComplexSimplicalMap" :<=>:
    And [ valid csx
        , valid csy
        , valid $ cpxsComplexMap f
        ]

n :: Any N4
n = attest

a = complex [Set "ad"]
b = complex [Set "abc",Set "bcd",Set "ad"]

f :: s ~ []
  => Any n -> ComplexSimplicalMap s n (ComplexSimplical s n Char) (ComplexSimplical s n Char) 
f n = ComplexSimplicalMap (singularComplex n a) (singularComplex n b) (OrdMap id)

--------------------------------------------------------------------------------
-- cpxsChainMapRep -

cpxsChainMapRep :: ( Ring r, Commutative r, Simplical s, Typeable s
                   , Entity (s x), Ord (s x)
                   , Entity (s y), Ord (s y)
                   )
  => ComplexSimplicalMap s n (ComplexSimplical s n x) (ComplexSimplical s n y)
  -> FinList (n+3) (Representable r (ChainHom r s) (Chain r s x) (Chain r s y))
cpxsChainMapRep (ComplexSimplicalMap csx csy f)
  = amap1 (uncurry (rep f)) (amap1 snd (cpxsxs csx) `F.zip` amap1 snd (cpxsxs csy)) where

  rep :: ( Ring r, Commutative r, Simplical s, Typeable s
         , Entity (s x), Ord (s x), Entity (s y), Ord (s y)
         )
    => OrdMap x y -> Set (s x) -> Set (s y)
    -> Representable r (ChainHom r s) (Chain r s x) (Chain r s y)
  rep f ssx ssy = chainHomRep (ChainMap ssx ssy f)

cpxsChainMapRepZ :: ( r ~ Z, Simplical s, Typeable s
                    , Entity (s x), Ord (s x)
                    , Entity (s y), Ord (s y)
                    )
  => ComplexSimplicalMap s n (ComplexSimplical s n x) (ComplexSimplical s n y)
  -> FinList (n+3) (Representable r (ChainHom r s) (Chain r s x) (Chain r s y))
cpxsChainMapRepZ = cpxsChainMapRep
