
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
-- Module      : OAlg.Homology.SimplicalComplex
-- Description : complexes of simplices over a complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- complexes of simplices over a complex. 
module OAlg.Homology.SimplicalComplex
  (
  ) where

import Control.Monad

import Data.Typeable

import Data.List as L (zip,(++),repeat)

import OAlg.Prelude

-- import OAlg.Structure.Fibred
-- import OAlg.Structure.Additive
-- import OAlg.Structure.Vectorial
-- import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Ring

-- import OAlg.Hom.Fibred
-- import OAlg.Hom.Additive
-- import OAlg.Hom.Vectorial

import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F
import OAlg.Entity.Sequence.Set
-- import OAlg.Entity.Sequence.Graph
-- import OAlg.Entity.Sum
-- import OAlg.Entity.Matrix

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.Chain

--------------------------------------------------------------------------------
-- SimplicalComplex -

-- | complexe of simplices over a given complex.
--
-- __Properties__ Let @'SimplicalComplex' c zssx@ be in @'SimplicalComplex' __s__ __n__ __x__@, then
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
data SimplicalComplex s n x
  = SimplicalComplex (Complex x) (FinList (n+3) (Z,Set (s x)))
  deriving (Show,Eq,Ord)

instance (Simplical s, Entity (s x), Ord (s x), Entity x, Ord x)
  => Validable (SimplicalComplex s n x) where
  valid (SimplicalComplex c zssx) = Label "SimplicalComplex" :<=>:
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
  => Entity (SimplicalComplex s n x)

--------------------------------------------------------------------------------
-- simplicalComplexSet -

simplicalComplexSet :: Any n -> Complex x -> SimplicalComplex Set n x
simplicalComplexSet n c@(Complex zssx) = SimplicalComplex c (zssx' n (-1) ssx) where
  ssx = amap1 snd zssx L.++ L.repeat setEmpty

  zssx' :: Any n -> Z -> [Set (Set x)] -> FinList (n+3) (Z,Set (Set x))
  zssx' W0 z (ssx:ssx':ssx'':_) = (z,ssx):|(succ z,ssx'):|(succ $ succ z,ssx''):|Nil
  zssx' (SW n) z (ssx:ssxs)     = (z,ssx):|zssx' n (succ z) ssxs
  zssx' _ _ _                   = throw $ ImplementationError "simplicalComplexSet.zssx'"
