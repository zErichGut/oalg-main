
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
    Chain, ch, boundary, chainMap

    -- * Chain Homomorphism
  , ChainHom(..), chainHomRep
  ) where

import Control.Monad

import Data.Typeable

import Data.List as L (zip,(++))

import OAlg.Prelude

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring

import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Vectorial

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sum
import OAlg.Entity.Matrix
import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Set -

deriving instance (Ord i, Ord x) => Ord (Graph i x)

--------------------------------------------------------------------------------
-- setDifference -
setDifference :: Ord x => Set x -> Set x -> Set x
setDifference (Set xs) (Set ys) = Set $ diff xs ys where
  diff [] _          = []
  diff xs []         = xs
  diff (x:xs) (y:ys) = case x `compare` y of
    LT -> x : diff xs (y:ys)
    EQ -> diff xs ys
    GT -> diff (x:xs) ys

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Chain -

-- | chains as a formal sum of simplices.
type Chain r s x = SumSymbol r (s x)

--------------------------------------------------------------------------------
-- ch -

-- | simplex as a chain.
ch :: (Ring r, Commutative r, Entity (s x), Ord (s x)) => s x -> Chain r s x
ch = sy

--------------------------------------------------------------------------------
-- rAlt -

rAlt :: Ring r => [r]
rAlt = za rOne where za i = i:za (negate i)

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary operator of chains.
boundary :: (Ring r, Commutative r, Simplical s, Entity (s x), Ord (s x))
  => Chain r s x -> Chain r s x
boundary = ssySum (bdr rAlt) where
  bdr :: Simplical s => [r] -> s x -> LinearCombination r (s x)
  bdr rs s = LinearCombination (rs `zip` faces s)

--------------------------------------------------------------------------------
-- chainMap -

chainMap :: (Ring r, Commutative r, Simplical s, Entity (s y), Ord (s y))
  => OrdMap x y -> Chain r s x -> Chain r s y
chainMap f = ssySum (chMap f) where
  chMap :: (Ring r, Simplical s) => OrdMap x y -> s x -> LinearCombination r (s y)
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
    :: (Entity (s x), Ord (s x))
    => Set (s x) -> Set (s x)
    -> ChainHom r s (Chain r s x) (Chain r s x)
  ChainMap
    :: (Entity (s x), Ord (s x), Entity (s y), Ord (s y))
    => Set (s x) -> Set (s y) -> OrdMap x y
    -> ChainHom r s (Chain r s x) (Chain r s y)

--------------------------------------------------------------------------------
-- ChainHom - Hom (Vec r) -

instance (Ring r, Commutative r, Simplical s) => Applicative (ChainHom r s) where
  amap (Boundary _ _)   = boundary
  amap (ChainMap _ _ f) = chainMap f

instance Show (ChainHom r s x y) where
  show (Boundary s s')    = "Boundary (" ++ show s ++ ") (" ++ show s' ++ ")"
  show (ChainMap sx sy _) = "ChainMap (" ++ show sx ++ ") (" ++ show sy ++ ")"
instance Show2 (ChainHom r s)

instance Simplical s => Eq (ChainHom r s x y) where
  Boundary s s' == Boundary t t' = s == t && s' == t'
  ChainMap sx sy f == ChainMap sx' sy' f'
    = sx == sx' && sy == sy' && and [amap1 f s == amap1 f' s | s <- setxs sx]
  _ == _ = False
instance Simplical s => Eq2 (ChainHom r s)

instance Simplical s => Validable (ChainHom r s x y) where
  valid (Boundary ssx ssx') = Label "Boundary" :<=>:
    And [ valid ssx
        , valid ssx'
        , Label "1" :<=>: let fs = faces' ssx in
            (fs `isSubSet` ssx') :?> Params ["fs":= show (fs `setDifference` ssx')]
        ]
  valid (ChainMap ssx ssy f) = Label "ChainMap" :<=>:
    And [ valid ssx
        , valid ssy
        , Label "2" :<=>: let ssy' = amap1 (OrdMap $ amap1 f) ssx in
            (ssy' `isSubSet` ssy) :?> Params ["ssy'" := show (ssy' `setDifference` ssy)]
        ]
instance Simplical s => Validable2 (ChainHom r s)

instance (Simplical s, Typeable r, Typeable s, Typeable x, Typeable y)
  => Entity (ChainHom r s x y)
instance (Simplical s, Typeable r, Typeable s) => Entity2 (ChainHom r s)

instance (Ring r, Commutative r, Simplical s, Typeable s) => Morphism (ChainHom r s) where
  type ObjectClass (ChainHom r s) = Vec r
  homomorphous (Boundary _ _)   = Struct :>: Struct
  homomorphous (ChainMap _ _ _) = Struct :>: Struct

instance (Ring r, Commutative r, Simplical s, Typeable s) => EmbeddableMorphism (ChainHom r s) Fbr
instance (Ring r, Commutative r, Simplical s, Typeable s) => EmbeddableMorphism (ChainHom r s) Typ
instance (Ring r, Commutative r, Simplical s, Typeable s) => EmbeddableMorphismTyp (ChainHom r s)
instance (Ring r, Commutative r, Simplical s, Typeable s) => HomFibred (ChainHom r s) where
  rmap (Boundary _ _)   = const ()
  rmap (ChainMap _ _ _) = const ()

instance (Ring r, Commutative r, Simplical s, Typeable s) => EmbeddableMorphism (ChainHom r s) Add
instance (Ring r, Commutative r, Simplical s, Typeable s) => HomAdditive (ChainHom r s)

instance (Ring r, Commutative r, Simplical s, Typeable s) => EmbeddableMorphism (ChainHom r s) (Vec r)
instance (Ring r, Commutative r, Simplical s, Typeable s) => HomVectorial r (ChainHom r s)

--------------------------------------------------------------------------------
-- chainHomRep -

chainHomRep
  :: (Ring r, Commutative r, Simplical s, Typeable s)
  => ChainHom r s (Chain r s x) (Chain r s y)
  -> Representable r (ChainHom r s) (Chain r s x) (Chain r s y)
chainHomRep h@(Boundary s s')    = Representable h s s'
chainHomRep h@(ChainMap sx sy _) = Representable h sx sy

