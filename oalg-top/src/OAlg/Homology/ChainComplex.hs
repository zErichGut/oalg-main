
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Homology.ChainComplex
-- Description : definition of a chain complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'ChainComplex'.
module OAlg.Homology.ChainComplex
  (

    -- * Chain Complex
    chainComplex, chainComplex', ChainComplex(..)
  , ChainComplexType(..), Regularity(..), BoundaryOperator
  , ccxDiagram, ccxHead, ccxTail

    -- ** Representation
  , ccxRepMatrix, ccxCards

    -- * Homomorphsim
  , chainComplexHom, chainComplexHomZ
  , ChainComplexHom(..)
  , MapOperator

    -- ** Representaiton
  , ccxRepMatrixHom, ccxCardsHom

  ) where

import Data.Typeable
import Data.List as L (repeat,(++),zip) 

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Additive
import OAlg.Structure.Algebraic

import OAlg.Entity.Diagram as D
import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix hiding (Transformation(..))

import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator as C
import OAlg.Homology.Simplical

--------------------------------------------------------------------------------
-- toFinList3 -

-- | maps a infinite list to a finite list of @__n__ + 3@.
toFinList3 :: Any n -> [x] -> FinList (n+3) x
toFinList3 W0 (x:x':x'':_) = x:|x':|x'':|Nil
toFinList3 (SW n) (x:xs)   = x :| toFinList3 n xs
toFinList3 _ _             = throw $ ImplementationError "toFinList3"

--------------------------------------------------------------------------------
-- ccxSimplices -

-- | sequence of sets of simplices over the given complex.
--
-- __Property__ Let @n@ be in @'Any' __n__@ and @c@ in @'Complex' __x__@, then holds:
--
--  (1) For all @(z,ssx)@ in @'ccxSimplices' n c@ and @s@ in @ssx@ holds:
--
--    (1) @'dimension' s '==' z@ 
--
--    (2) @s@ is in @ssx@ iff @'vertices' s@ is in @c@.
ccxSimplices :: Simplical s x => Any n -> Complex x -> FinList (n+3) (Z,Set (s x))
ccxSimplices n c = case mSet (ccs n c) of
  (Just Refl,_) -> ccsSet n c -- more economic and faster
  (Nothing,s)   -> s
  where

    mSet :: Typeable s => FinList n (Z,Set (s x)) -> (Maybe (s :~: Set),FinList n (Z,Set (s x)))
    mSet s = (eqT,s)
  
    ccsSet :: Ord x => Any n -> Complex x -> FinList (n+3) (Z,Set (Set x))
    ccsSet n c = toFinList3 n ([-1..] `L.zip` ssx) where
      ssx = (amap1 snd $ gphxs $ cpxSimplices c) L.++ L.repeat empty
  
    ccs :: Simplical s x => Any n -> Complex x -> FinList (n+3) (Z,Set (s x))
    ccs n c = toFinList3 n ([-1..] `L.zip` ssx) where
      ssx = amap1 (filter (elg c))
          $ ((amap1 snd $ gphxs $ simplices $ cpxVertices c) L.++ L.repeat empty  )
  
      elg :: Simplical s x => Complex x -> s x -> Bool
      elg c = cpxElem c . vertices

--------------------------------------------------------------------------------
-- Regular -

-- | concept of regularity.
data Regularity = Restricted | Regular | Extended deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- ChainComplexType -

data ChainComplexType t where
  ChainComplexStandard :: ChainComplexType Restricted
  ChainComplexExtended :: ChainComplexType Regular

deriving instance Show (ChainComplexType t)
deriving instance Eq (ChainComplexType t)

--------------------------------------------------------------------------------
-- BoundaryOperator -

-- | boundary operator.
type BoundaryOperator r s x = ChainOperatorRepSum r s (ChainG r s x) (ChainG r s x)

--------------------------------------------------------------------------------
-- ChainComplex -

-- | chain complex.
--
-- __Property__ Let @v'ChainComplex' t zssx@ be in @t'ChainComplex' __t r s n x__@
-- for @'Simplical' __s x__@, then for all @(_,ssx0) .. (z',ssx')':|'(z,ssx) ..@ in @zssx@ holds:
--
-- (1) @faces' ssx@ is a subset of @ssx'@ for all
--  @.. (_,ssx')':|'(_,ssx) ..@ in @'tail' zssx@.
--
-- (2) If @t@ matches 'ChainComplexStandard' then @ssx '==' 'empty'@
-- else @faces' ssx@ is a subset of @ssx'@ for all @(_,ssx')':|'(_,ssx) ..@ in @zssx@.
data ChainComplex t r s n x
  = ChainComplex (ChainComplexType t) (Diagram (Chain To) (n+3) (n+2) (BoundaryOperator r s x))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccxDiagram -

ccxDiagram :: ChainComplex t r s n x -> Diagram (Chain To) (n+3) (n+2) (BoundaryOperator r s x)
ccxDiagram (ChainComplex _ d) = d

--------------------------------------------------------------------------------
-- chainComplex -

-- | the chain complex of the boundary operators, where in the t'Extended' case the first operator
-- is addapted to @'zero'@ with an empty 'end'.
chainComplex :: (Ring r, Commutative r, Ord r, Simplical s x)
  => ChainComplexType t -> Any n -> Complex x -> ChainComplex t r s n x
chainComplex t n c
  = ChainComplex t (toDgm t $ toBndOpr $ amap1 snd $ ccxSimplices n c) where

  toBndOpr :: (Ring r, Commutative r, Ord r, Simplical s x)
    => FinList (n+1) (Set (s x)) -> FinList n (BoundaryOperator r s x)
  toBndOpr (_:|Nil) = Nil
  toBndOpr (sx:|sx':|sxs) = chors (Representable Boundary sx' sx) :| toBndOpr (sx':|sxs)

  -- converts to a Chain To diagram by possibly addapting the first operator to zero.
  toDgm :: (Ring r, Commutative r, Ord r, Simplical s x)
    => ChainComplexType t
    -> FinList (n+1) (BoundaryOperator r s x)
    -> Diagram (Chain To) (n+2) (n+1) (BoundaryOperator r s x)
  toDgm t (d:|ds) = DiagramChainTo (end d') (d':|ds) where
    d' = case t of
      ChainComplexExtended -> d              -- no addaption
      ChainComplexStandard -> zeroEmptyEnd d -- to zero with empty end, but same start

  zeroEmptyEnd :: (Ring r, Commutative r, Ord r, Simplical s x)
    => BoundaryOperator r s x -> BoundaryOperator r s x
  zeroEmptyEnd d = zero (start d,empty) 

chainComplex' :: Simplical s x
  => q s -> ChainComplexType t -> Any n -> Complex x -> ChainComplex t Z s n x
chainComplex' _ = chainComplex

{-
t = ChainComplexStandard
n = attest :: Any N4
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N
s = Proxy :: Proxy Asc
cmf = ComplexMapNgl a b (Map f)
cmfHom = chainComplexHomZ t n cmf

f c = case c of
  'a' -> 0
  'b' -> 1
  'c' -> 2
  'd' -> 0
  _   -> error "undefined"
-}

--------------------------------------------------------------------------------
-- ccxHead -

ccxHead :: ChainComplex t r s n x -> ChainComplex t r s N0 x
ccxHead (ChainComplex t (DiagramChainTo e (d0:|d1:|_)))
  = ChainComplex t (DiagramChainTo e (d0:|d1:|Nil))

--------------------------------------------------------------------------------
-- ccxTail -

ccxTail :: (AlgebraicSemiring r, Ring r, Ord r, Simplical s x)
  => ChainComplex t r s (n+1) x -> ChainComplex Regular r s n x
ccxTail (ChainComplex _ (DiagramChainTo _ (d0:|ds)))
  = ChainComplex ChainComplexExtended (DiagramChainTo (start d0) ds)

--------------------------------------------------------------------------------
-- ccxRepMatrix -

-- | the representation matrices of the boundary operators.
ccxRepMatrix :: (AlgebraicSemiring r, Ring r, Ord r, Simplical s x)
  => ChainComplex t r s n x -> ConsecutiveZero To n (Matrix r)
ccxRepMatrix (ChainComplex _ c) = ConsecutiveZero $ dgMap ChorsRepMatrix c

--------------------------------------------------------------------------------
-- ccxCards -

-- | the cardinalities of the base of the boundary operators. 
ccxCards :: (Ring r, Ord r, AlgebraicSemiring r, Simplical s x)
  => ChainComplex t r s n x -> Cards r n
ccxCards (ChainComplex _ c)
  = Cards $ DiagramDiscrete $ dgPoints $ dgMap ChorsCards c

--------------------------------------------------------------------------------
-- MapOperator -

-- | mapping operator.
type MapOperator r s x y = ChainOperatorRepSum r s (ChainG r s x) (ChainG r s y)

--------------------------------------------------------------------------------
-- ChainComplexHom -

-- | homomorphism of chain complexes.
data ChainComplexHom t r s n x y
  = ChainComplexHom
      (ChainComplex t r s n x)
      (ChainComplex t r s n y)
      (FinList (n+3) (MapOperator r s x y))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- chainComplexHom -

-- | the induced homomorphsim of chain complexes.
chainComplexHom :: (Ring r, Ord r, AlgebraicSemiring r, Homological s x y)
  => ChainComplexType t -> Any n -> ComplexMap s (Complex x) (Complex y) -> ChainComplexHom t r s n x y
chainComplexHom t n f = ChainComplexHom a b hs where
  a = chainComplex t n (cpmDomain f)
  b = chainComplex t n (cpmRange f)
  hs = amap1 (uncurry $ toMapOpr $ cpmMap f) (dgPoints (ccxDiagram a) `F.zip` dgPoints (ccxDiagram b))

  toMapOpr :: (Ring r, Ord r, AlgebraicSemiring r, Homological s x y)
    => Map EntOrd x y -> Set (s x) -> Set (s y) -> MapOperator r s x y
  toMapOpr f sx sy = chors (Representable (ChainMap f) sx sy)

-- | the induced homomorphsim of chain complexes within 'Z'.
chainComplexHomZ ::Homological s x y
  => ChainComplexType t -> Any n -> ComplexMap s (Complex x) (Complex y) -> ChainComplexHom t Z s n x y
chainComplexHomZ = chainComplexHom

--------------------------------------------------------------------------------
-- ccxRepMatrixHom -

-- | the homomrophism of the representation matrices of the boundary operators.
ccxRepMatrixHom :: (Ring r, Ord r, AlgebraicSemiring r, Homological s x y)
  => ChainComplexHom t r s n x y -> ConsecutiveZeroHom To n (Matrix r)
ccxRepMatrixHom (ChainComplexHom a b hs) = ConsecutiveZeroHom (DiagramTrafo a' b' ts) where
  ConsecutiveZero a' = ccxRepMatrix a
  ConsecutiveZero b' = ccxRepMatrix b
  ts = amap1 chorsRepMatrix hs

--------------------------------------------------------------------------------
-- ccxCardsHom -

-- | the cardinalities the mapping operators.
ccxCardsHom :: (Ring r, Ord r, AlgebraicSemiring r, Simplical s x, Simplical s y)
  => ChainComplexHom t r s n x y -> CardsHom r n
ccxCardsHom (ChainComplexHom a b _) = CardsHom t where
  Cards a' = ccxCards a
  Cards b' = ccxCards b
  t = DiagramTrafo a' b' $ amap1 (uncurry ((:>))) (dgPoints a' `F.zip` dgPoints b')
