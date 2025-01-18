
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
-- Module      : OAlg.Homology.Complex
-- Description : complex of simplices over a set complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- complex of simplices over a set complex.
module OAlg.Homology.Complex
  (
  ) where

import Data.Typeable

import Data.List as L (zip,(++),repeat)

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Vectorial
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

-- import OAlg.Hom.Fibred
-- import OAlg.Hom.Additive
-- import OAlg.Hom.Vectorial

import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
-- import OAlg.Entity.Sum
import OAlg.Entity.Matrix

import OAlg.Homology.Simplical
import OAlg.Homology.SetComplex
import OAlg.Homology.Chain


--------------------------------------------------------------------------------
-- Complex -

-- | finite complexe of simplices over a set complex.
--
-- __Properties__ Let @c = 'Complex' sc zxs@ be in @'Complex' __s__ __n__ __x__@, then
-- holds:
--
-- (1) @z0 '==' -1@ where @(z0,_) = 'head' zxs@.
--
-- (2) For all @(z,'Set' sxs)@ in @zxs@ and @sx@ in @sxs@ holds:
--
--     (1) @'dimension' sx '==' z@.
--
--     (2) @'verteices' sx@ is an element of @sc@.
--
-- (3) For all @..(z,su)':'(z',sv)..@ in @zsx@ holds:
--
--    (1) @z' '==' z '+' 1@.
--
--    (2) @'faces'' sv'@ is a subset of @su@.
--
-- (4) If @sx@ is in @__s__ __x__@ with @'vertices' sx@ is in @sc@, then @sx@ is in @c@.
data Complex s n x
  = Complex (SetComplex x) (FinList (n+3) (Z,Set (s x)))
  deriving (Show,Eq,Ord)

instance (Simplical s x, Entity x, Ord x) => Validable (Complex s n x) where
  valid (Complex c ((z,sx):|zsx')) = Label "Complex" :<=>:
    And [ valid c
        , Label "1" :<=>: (z == -1) :?> Params ["z0":=show z]
        , vldDimension cElem z sx
        , vldFaces cElem z sx zsx'
        ]
    where
      cElem = scxElem c

      vldDimension :: Simplical s x => (Set x -> Bool) -> Z -> Set (s x) -> Statement
      vldDimension _ _ (Set []) = SValid
      vldDimension cElem z (Set (sx:sxs))
        = And [ Label "2.1" :<=>: (dimension sx == z) :?> Params ["sx":= show sx]
              , Label "2.2" :<=>:  cElem (vertices sx) :?> Params ["sx":= show sx]
              , vldDimension cElem z (Set sxs)
              ]

      vldFaces :: Simplical s x
        =>(Set x -> Bool) -> Z -> Set (s x) -> FinList n (Z,Set (s x)) -> Statement
      vldFaces _ _ _ Nil = SValid
      vldFaces cElem z su ((z',sv):|zsx)
        = And [ vldDimension cElem z' sv
              , Label "3.1" :<=>: (z' == succ z) :?> Params ["z":=show z, "z'":=show z']
              , Label "3.2" :<=>: let fsv = faces' sv in
                  (fsv <<= su) :?> Params ["fsv":= show (fsv // su)]
              , vldFaces cElem z' sv zsx
              ]

instance (Simplical s x, Typeable s, Entity x, Ord x, Typeable n)
  => Entity (Complex s n x)

--------------------------------------------------------------------------------
-- cpxxs -

cpxxs :: Complex s n x -> FinList (n+3) (Z,Set (s x))
cpxxs (Complex _ zssx) = zssx

--------------------------------------------------------------------------------
-- toFinList3 -

-- | maps a infinite list to a finite list of @__n__ + 3@.
toFinList3 :: Any n -> [x] -> FinList (n+3) x
toFinList3 W0 (x:x':x'':_) = x:|x':|x'':|Nil
toFinList3 (SW n) (x:xs)   = x :| toFinList3 n xs
toFinList3 _ _             = throw $ ImplementationError "toFinList3"

--------------------------------------------------------------------------------
-- simplicalComplex -

-- | the embedding of a complex of set-simplices.
simplicalComplex :: Ord x => Any n -> SetComplex x -> Complex Set n x
simplicalComplex n c@(SetComplex (Graph zssx))
  = Complex c (toFinList3 n ([-1..] `L.zip` ssx))
  where ssx = amap1 snd zssx L.++ L.repeat empty

--------------------------------------------------------------------------------
-- singularComplex -

-- | complex of simplices of the given set complex, containing maybe singular simplices.
--
-- __Note__
-- (1) The cardinality of the simplical sets __explodes__ for example @__s__ = []@.
--
-- (2) The result of 'singularComplex' for @__s__ = 'Set'@ and 'simplicalComplex' are equal,
-- but 'simplicalComplex' is faster.
singularComplex :: (Simplical s x, Entity x, Ord x) => Any n -> SetComplex x -> Complex s n x
singularComplex n c = Complex c (toFinList3 n ([-1..] `L.zip` ssx)) where
  ssx = amap1 (filter (elg c)) ((amap1 snd $ gphxs $ simplices $ scxVertices c) L.++ L.repeat empty)

  elg :: (Simplical s x, Entity x, Ord x) => SetComplex x -> s x -> Bool
  elg c = scxElem c . vertices


cpxl :: Any n -> N -> Complex [] n N
cpxl n m = singularComplex n (setComplex [Set [1..m]])

cpxa :: Any n -> N -> Complex Asc n N
cpxa n m = singularComplex n (setComplex [Set [1..m]])

cpxs :: Any n -> N -> Complex Set n N
cpxs n m = singularComplex n (setComplex [Set [1..m]])

cpxs' :: Any n -> N -> Complex Set n N
cpxs' n m = simplicalComplex n (setComplex [Set [1..m]])

--------------------------------------------------------------------------------
-- cpxBoundaryRep -

-- | representing boundary operator according to the given comlex.
--
-- __Note__ From the 'Complex'-property 3.2 follwos, that if the given complex is 'valid', then its
-- boundary representations given by 'cpxBoundaryRep' is 'valid'
cpxBoundaryRep :: (Ring r, Commutative r, Simplical s x)
  => Complex s n x
  -> FinList (n+2) (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
cpxBoundaryRep c = repBoundary (amap1 snd $ cpxxs c) where
  repBoundary :: (Ring r, Commutative r, Simplical s x)
    => FinList (n+1) (Set (s x))
    -> FinList n (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
  repBoundary (_:|Nil)       = Nil
  repBoundary (sx:|sx':|sxs) = chainHomRep (Boundary sx' sx) :| repBoundary (sx':|sxs)

cpxBoundaryRepZ :: (r ~ Z, Simplical s x)
  => Complex s n x
  -> FinList (n+2) (Representable r (ChainHom r s) (Chain r s x) (Chain r s x))
cpxBoundaryRepZ = cpxBoundaryRep

--------------------------------------------------------------------------------
-- ComplexMap -

-- | mapping between complex of simplices, where the underlying map induces a mapping between the two
-- given simplex sets.
--
-- __Property__ Let @'ComplexMap' csx csy f@ be in
-- @'ComplexMap' __s__ __n__ (Complex __s__ __n__ __x__) (Complex __s__ __n__ __y__)@ for a
-- 'SimplicalTransformable __s__ __x__ __y__@ structure,then holds for all simplices @s@ in @csx@:
-- @'amap1' f s@ is an element of @csy@.
--
-- __Note__ Because of the 'SimplicalTransformable'-property and the 'Complex'-property 4 it is
-- sufficient that the induced set-complex map - given by 'cpxetComplexMap' - is 'valid'. 
data ComplexMap s n x y where
  ComplexMap
    :: Homological s x y
    => Complex s n x -> Complex s n y
    -> Map EntOrd x y
    -> ComplexMap s n (Complex s n x) (Complex s n y)

-- deriving instance (Show x, Show y) => Show (ComplexMap s n (Complex s n x) (Complex s n y))

--------------------------------------------------------------------------------
-- cpxetComplexMap -

cpxetComplexMap :: ComplexMap s n (Complex s n x) (Complex s n y)
  -> SetComplexMap (SetComplex x) (SetComplex y)
cpxetComplexMap (ComplexMap (Complex cx _) (Complex cy _) f)
  = SetComplexMap cx cy f

--------------------------------------------------------------------------------
-- ComplexMap - Entity -

instance SimplicalTransformable s x y
  => Validable (ComplexMap s n (Complex s n x) (Complex s n y)) where
  valid f@(ComplexMap csx csy (Map _)) = Label "ComplexMap" :<=>:
    And [ valid csx
        , valid csy
        , valid $ cpxetComplexMap f
        ]
{-
n :: Any N4
n = attest

a = complex [Set "ad"]
b = complex [Set "abc",Set "bcd",Set "ad"]

f :: s ~ []
  => Any n -> ComplexMap s n (Complex s n Char) (Complex s n Char) 
f n = ComplexMap (singularComplex n a) (singularComplex n b) (OrdMap id)
-}

--------------------------------------------------------------------------------
-- cpxChainMapRep -

cpxChainMapRep :: (Ring r, Commutative r, SimplicalTransformable s x y)
  => ComplexMap s n (Complex s n x) (Complex s n y)
  -> FinList (n+3) (Representable r (ChainHom r s) (Chain r s x) (Chain r s y))
cpxChainMapRep (ComplexMap csx csy f)
  = amap1 (uncurry (rep f)) (amap1 snd (cpxxs csx) `F.zip` amap1 snd (cpxxs csy)) where

  rep :: (Ring r, Commutative r, SimplicalTransformable s x y)
    => Map EntOrd x y -> Set (s x) -> Set (s y)
    -> Representable r (ChainHom r s) (Chain r s x) (Chain r s y)
  rep f ssx ssy = chainHomRep (ChainMap ssx ssy f)

cpxChainMapRepZ :: (r ~ Z, SimplicalTransformable s x y)
  => ComplexMap s n (Complex s n x) (Complex s n y)
  -> FinList (n+3) (Representable r (ChainHom r s) (Chain r s x) (Chain r s y))
cpxChainMapRepZ = cpxChainMapRep


a = setComplex [Set [(0,0),(0,1),(1,1)],Set [(0,0),(1,0),(1,1)]] :: SetComplex (N,N)
b = setComplex [Set [0,1]] :: SetComplex N

p1 = SetComplexMap a b (Map fst)
p2 = SetComplexMap a b (Map snd)

f :: s ~ [] => Any n -> ComplexMap s n (Complex s n (N,N)) (Complex s n N) 
f n = ComplexMap (singularComplex n a) (singularComplex n b) (Map snd)
