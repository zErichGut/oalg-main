
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
    chainComplexOperators, Regular(..), ChainComplex
  , ccpRepMatrix, ccpCards

    -- * Chain Complex Trafo
  , chainComplexOperatorsHom, ChainComplexHom
  , ccpHomRepMatrix, ccpHomCardsHom

  , bndZSet, bndZAsc, bndZLst

  ) where

import Control.Monad

import Data.Typeable
import Data.List as L (repeat,(++),zip) 

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Algebraic

import OAlg.Entity.Diagram as D
import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix hiding (Transformation(..))

import OAlg.Hom.Distributive

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
--  (1) For @(z,ssx)@ in @'ccxSimplices' n c@ holds: @'dimension' s '==' z@ for all @s@ in @ssx@.
--
--  (2) For all @s@ in @__s__ __x__@ holds: @s@ is in @'ccxSimplices' n c@ iff
--  @'vertices' s@ is in @c@.
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

-- | kind of the generated 'ChainComplex' of 'BoundaryOperator's. 'Extended' defines the last
-- boundary operator as the extended one and 'Regular' defines it as @0@. 
data Regular = Regular | Extended deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- ChainComplex -

-- | chain complex.
type ChainComplex = ConsecutiveZero To

--------------------------------------------------------------------------------
-- chainComplexOperators -

-- | the chain complex of the boundary operators, where in the v'Regular' case the first operator
-- is addapted to @'zero'@ with an empty 'end'.
chainComplexOperators :: (Ring r, Commutative r, Ord r)
  => Struct (Smpl s) x -> Regular -> Any n -> Complex x
  -> ChainComplex n (ChainOperator r s)
chainComplexOperators Struct r n c
  = ConsecutiveZero $ toDgm r $ toBndOpr $ amap1 snd $ ccxSimplices n c where

  toBndOpr :: (Ring r, Commutative r, Ord r, Simplical s x)
    => FinList (n+1) (Set (s x)) -> FinList n (ChainOperator r s)
  toBndOpr (_:|Nil) = Nil
  toBndOpr (sx:|sx':|sxs) = chopr (Representable Boundary sx' sx) :| toBndOpr (sx':|sxs)

  -- converts to a Chain To diagram by possibly addapting the first operator to zero.
  toDgm :: (Ring r, Commutative r, Ord r, Typeable s)
    => Regular
    -> FinList (n+1) (ChainOperator r s) -> Diagram (Chain To) (n+2) (n+1) (ChainOperator r s)
  toDgm r (ChainOperator d:|ds) = DiagramChainTo (end d') (d':|ds) where
    d' = ChainOperator $ case r of
      Extended -> d              -- no addaption
      Regular  -> zeroEmptyEnd d -- to zero with empty end, but same start
      
  zeroEmptyEnd :: (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
    => ChainOperatorRepSum r s (ChainG r s x) (ChainG r s y)
    -> ChainOperatorRepSum r s (ChainG r s x) (ChainG r s y)
  zeroEmptyEnd d = zero (fst $ root d,empty) 


bndZSet :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z Set)
bndZSet = chainComplexOperators Struct

bndZAsc :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z Asc)
bndZAsc = chainComplexOperators Struct

bndZLst :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> ChainComplex n (ChainOperator Z [])
bndZLst = chainComplexOperators Struct


--------------------------------------------------------------------------------
-- ccpRepMatrix -

ccpRepMatrix :: (AlgebraicSemiring r, Ring r, Ord r, Typeable s)
  => ChainComplex n (ChainOperator r s) -> ChainComplex n (Matrix r)
ccpRepMatrix = cnzMapCov (homDisjOpDst ChoprRepMatrix)

--------------------------------------------------------------------------------
-- ccpCards -

-- | the cardinalities of the consecutive 'SimplexSet's of the given chain complex.
ccpCards :: (Ring r, Commutative r, Ord r, Typeable s)
  => ChainComplex n (ChainOperator r s) -> Cards r n
ccpCards c = Cards $ DiagramDiscrete $ cnzPoints $ cnzMapCov (homDisjOpDst choprCardsOrnt) c

--------------------------------------------------------------------------------
-- ChainComplexHom -

-- | transformation between chain complexes.
type ChainComplexHom = ConsecutiveZeroHom To

--------------------------------------------------------------------------------
-- chainComplexOperatorsHom -

eqSetType :: (Typeable x, Typeable x', Typeable y, Typeable y')
  => Map EntOrd x y -> Set (s x') -> Set (s y') -> Maybe (x :~: x',y :~: y')
eqSetType f sx sy = do
  d <- eqDom f sx
  r <- eqRng f sy
  return (d,r)
  
  where
    eqDom :: (Typeable x, Typeable x') => Map EntOrd x y -> Set (s x') -> Maybe (x :~: x')
    eqDom _ _ = eqT

    eqRng :: (Typeable y, Typeable y') => Map EntOrd x y -> Set (s y') -> Maybe (y :~: y')
    eqRng _ _ = eqT

-- | the transformation of chain complexes.
chainComplexOperatorsHom :: (Ring r, Commutative r, Ord r)
  => Struct2 (Hmlg s) x y -> Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> ChainComplexHom n (ChainOperator r s)
chainComplexOperatorsHom Struct2 r n f = ConsecutiveZeroHom $ DiagramTrafo  a b fs where
  ConsecutiveZero a  = chainComplexOperators Struct r n (cpmDomain f)
  ConsecutiveZero b  = chainComplexOperators Struct r n (cpmRange f)
  fs = amap1 (uncurry $ toChnMap $ cpmMap f) $ dgPoints a `F.zip` dgPoints b

  toChnMap :: (Ring r, Commutative r, Ord r, Homological s x y)
    => Map EntOrd x y -> SimplexSet s -> SimplexSet s -> ChainOperator r s
  toChnMap f (SimplexSet sx) (SimplexSet sy) = case eqSetType f sx sy of
    Just (Refl,Refl) -> chopr (Representable (ChainMap f) sx sy)
    Nothing          -> throw $ ImplementationError "chainComplexOperatorsHom.toChnMap"

--------------------------------------------------------------------------------
-- ccpHomRepMatrix -

ccpHomRepMatrix :: (AlgebraicSemiring r, Ring r, Ord r, Typeable s)
  => ChainComplexHom n (ChainOperator r s) -> ChainComplexHom n (Matrix r)
ccpHomRepMatrix = cnzHomMapCov (homDisjOpDst ChoprRepMatrix)

--------------------------------------------------------------------------------
-- ccpHomCardsHom -

ccpHomCardsHom :: (Ring r, Commutative r, Ord r, Typeable s)
  => ChainComplexHom n (ChainOperator r s) -> CardsHom r n
ccpHomCardsHom t = CardsHom $ DiagramTrafo a b fs where
  ConsecutiveZeroHom (DiagramTrafo a' b' fs) = cnzHomMapCov (homDisjOpDst choprCardsOrnt) t
  a  = DiagramDiscrete $ dgPoints a'
  b  = DiagramDiscrete $ dgPoints b'


