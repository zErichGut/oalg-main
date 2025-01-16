
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
-- Module      : OAlg.Homology.Chain
-- Description : chains and there boundary.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- The boundary of a 'Chain'.
module OAlg.Homology.Chain
  (
    -- * Chain
    Chain, ch, chZ, boundary, chainMap

    -- * Chain Homomorphism
  , ChainHom(..), chainHomRep

  ) where

import Data.Typeable

import Data.List as L (zip,(++))

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum
import OAlg.Entity.Matrix

import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | a simplex as a @__r__@-chain.
ch :: (Ring r, Commutative r, Simplical s x) => s x -> Chain r s x
ch = sy

-- | a simplces as a 'Z'-chain.
chZ :: Simplical s x => s x -> Chain Z s x
chZ = ch

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s x)
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s x => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- chainMap -

chainMap :: (Ring r, Commutative r, SimplicalTransformable s x y)
  => Map EntOrd x y -> Chain r s x -> Chain r s y
chainMap f = ssySum (chMap f) where
  chMap :: (Ring r, SimplicalTransformable s x y) => Map EntOrd x y -> s x -> LinearCombination r (s y)
  chMap f sx = LinearCombination [(rOne,amap1 f sx)]

--------------------------------------------------------------------------------
-- ChainHom -

-- | homomorphism between chains.
--
-- __Property__ Let @h@ be in @'ChainHom' __r__ __s__ __x__ __y__@ where @r@ is a commutaitve ring
-- and @s@ a 'Simplical' structure, then holds:
--
-- (1) In case where @h@ matches @'Boundary' ssx ssx'@ then holds:
-- @'faces'' ssx@ is a subset of @ssx'@.
--
-- (2) In case where @h@ matches @'ChainMap' ssx ssy f@ then for all @sx@ in @ssx@ holds:
-- @'amap1' f sx@ is an element of @ssy@.
data ChainHom r s x y where
  Boundary
    :: Simplical s x
    => Set (s x) -> Set (s x)
    -> ChainHom r s (Chain r s x) (Chain r s x)
  ChainMap
    :: SimplicalTransformable s x y
    => Set (s x) -> Set (s y) -> Map EntOrd x y
    -> ChainHom r s (Chain r s x) (Chain r s y)

--------------------------------------------------------------------------------
-- ChainHom - Hom (Vec r) -

instance (Ring r, Commutative r) => Applicative (ChainHom r s) where
  amap (Boundary _ _)   = boundary
  amap (ChainMap _ _ f) = chainMap f

instance Show (ChainHom r s x y) where
  show (Boundary s s')    = "Boundary (" ++ show s ++ ") (" ++ show s' ++ ")"
  show (ChainMap sx sy _) = "ChainMap (" ++ show sx ++ ") (" ++ show sy ++ ")"
instance Show2 (ChainHom r s)

instance Eq (ChainHom r s x y) where
  Boundary s s' == Boundary t t' = s == t && s' == t'
  ChainMap sx sy f == ChainMap sx' sy' f'
    = sx == sx' && sy == sy' && and [amap1 f s == amap1 f' s | s <- setxs sx]
  _ == _ = False
instance Eq2 (ChainHom r s)

instance Validable (ChainHom r s x y) where
  valid (Boundary ssx ssx') = Label "Boundary" :<=>:
    And [ valid ssx
        , valid ssx'
        , Label "1" :<=>: let fs = faces' ssx in
            (fs <<= ssx') :?> Params ["fs":= show (fs // ssx')]
        ]
  valid (ChainMap ssx ssy f) = Label "ChainMap" :<=>:
    And [ valid ssx
        , valid ssy
        , Label "2" :<=>: let ssy' = amap1 (map f) ssx in
            (ssy' <<= ssy) :?> Params ["ssy'" := show (ssy' // ssy)]
        ]
    where map :: SimplicalTransformable s x y => Map EntOrd x y -> Map EntOrd (s x) (s y)
          map = Map . amap1
instance Validable2 (ChainHom r s)

instance (Typeable r, Typeable s, Typeable x, Typeable y)
  => Entity (ChainHom r s x y)

instance (Typeable r, Typeable s) => Entity2 (ChainHom r s)


instance (Ring r, Commutative r, Typeable s) => Morphism (ChainHom r s) where
  type ObjectClass (ChainHom r s) = Vec r
  homomorphous (Boundary _ _)   = Struct :>: Struct
  homomorphous (ChainMap _ _ _) = Struct :>: Struct

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Fbr
instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Typ
instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphismTyp (ChainHom r s)
instance (Ring r, Commutative r, Typeable s) => HomFibred (ChainHom r s) where
  rmap (Boundary _ _)   = const ()
  rmap (ChainMap _ _ _) = const ()

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) Add
instance (Ring r, Commutative r, Typeable s) => HomAdditive (ChainHom r s)

instance (Ring r, Commutative r, Typeable s) => EmbeddableMorphism (ChainHom r s) (Vec r)
instance (Ring r, Commutative r, Typeable s) => HomVectorial r (ChainHom r s)

--------------------------------------------------------------------------------
-- chainHomRep -

chainHomRep
  :: (Ring r, Commutative r, Typeable s)
  => ChainHom r s (Chain r s x) (Chain r s y)
  -> Representable r (ChainHom r s) (Chain r s x) (Chain r s y)
chainHomRep h@(Boundary s s')    = Representable h s s'
chainHomRep h@(ChainMap sx sy _) = Representable h sx sy

