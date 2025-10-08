
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
{-    
    -- * Chain Complex
    chainComplexOperators, Regular(..), ChainComplex
  , ccpRepMatrix, ccpCards

    -- * Chain Complex Trafo
  , chainComplexOperatorsHom, ChainComplexHom
  , ccpHomRepMatrix, ccpHomCardsHom

  , bndZSet, bndZAsc, bndZLst
-}
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
import OAlg.Entity.Sum.Definition
import OAlg.Entity.Sum.SumSymbol

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

-- | kind of the generated 'ChainComplex'. 'Truncated' defines the first
-- set of simplices to be 'empty'.
data Regular = Regular | Truncated deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- BoundaryOp -

type BoundaryOperator r s x = ChainOperatorRepSum r s (ChainG r s x) (ChainG r s x)

--------------------------------------------------------------------------------
-- ChainComplex -

-- | chain complex.
--
-- __Property__ Let @v'ChainComplex' r zssx@ be in @t'ChainComplex' __s n x__@
-- for @'Simplical' __s x__@, then for all @(_,ssx0) .. (z',ssx')':|'(z,ssx) ..@ in @zssx@ holds:
--
-- (1) If @r '==' 'Regular'@ holds: @faces' ssx@ is a subset of @ssx'@ for all
-- @.. (z',ssx')':|'(z,ssx) ..@ in @zssx@.
--
-- (2) If @r '==' 'Truncated'@ then holds:
--
--     (1) @ssx0@ is 'empty' weher @(_,ssx0) = 'head' zssx@.
--
--     (2) @faces' ssx@ is a subset of @ssx'@ for all
--     @.. (z',ssx')':|'(z,ssx) ..@ in @'tail' zssx@.
data ChainComplex r s n x
  = ChainComplex (Diagram (Chain To) (n+3) (n+2) (BoundaryOperator r s x))
  deriving (Show,Eq)
{-
--------------------------------------------------------------------------------
-- ccxTail -

ccxTail :: ChainComplex s (n+1) x -> ChainComplex s n x
ccxTail (ChainComplex _ ssxs) = ChainComplex Regular (tail ssxs)

--------------------------------------------------------------------------------
-- prpChainComplex -

-- | @'relChainComplexFaces' ssx' 
relChainComplexFaces :: Simplical s x => Regular -> FinList (n+2) (Z,Set (s x)) -> Statement
relChainComplexFaces r ((z',ssx'):|(z,ssx):|_) = case r of
  Regular   -> (faces' ssx  <<= ssx') :?> Params ["z":=show z]
  Truncated -> Label "Truncated" :<=>: (ssx' == empty) :?> Params ["z'":=show z'] 

relChainComplex :: Simplical s x => ChainComplex s n x -> Statement
relChainComplex c@(ChainComplex r zssxs)
  = relChainComplexFaces r zssxs && case zssxs of
      _:|zssx':|zssx:|Nil -> relChainComplexFaces Regular (zssx':|zssx:|Nil)
      _:|_:|_:|_:|_       -> relChainComplex (ccxTail c)

-- | validity according to t'ChainComplex'.
prpChainComplex :: Simplical s x => ChainComplex s n x -> Statement
prpChainComplex c = Prp "ChainComplex" :<=>: relChainComplex c

instance Simplical s x => Validable (ChainComplex s n x) where
  valid = prpChainComplex

--------------------------------------------------------------------------------
-- chainComplex -

-- | the induced chain complex.
chainComplex :: Simplical s x => Regular -> Any n -> Complex x -> ChainComplex s n x
chainComplex r n c = case r of
  Regular   -> cx
  Truncated -> trnc cx  
  where
    cx = ChainComplex r $ ccxSimplices n c
    trnc (ChainComplex _ zssxs) = ChainComplex Truncated ((-1,empty):|tail zssxs)

-- | the induced chain complex according to the given proxy type.
chainComplex' :: Simplical s x => q s -> Regular -> Any n -> Complex x -> ChainComplex s n x
chainComplex' _ = chainComplex

--------------------------------------------------------------------------------
-- ccxCards -

ccxCards :: ChainComplex s n x -> Cards r n 
ccxCards (ChainComplex _ zssxs) = Cards $ DiagramDiscrete $ amap1 (lengthN . snd) zssxs

c = complex [Set [0,1],Set [1,2],Set[0,2]] :: Complex N
cx = chainComplex' (Proxy :: Proxy []) Regular (attest :: Any N2) c
-}


--------------------------------------------------------------------------------
-- chainComplex -

-- | the chain complex of the boundary operators, where in the v'Regular' case the first operator
-- is addapted to @'zero'@ with an empty 'end'.
chainComplex :: (Ring r, Commutative r, Ord r)
  => Struct (Smpl s) x -> Regular -> Any n -> Complex x
  -> ChainComplex r s n x
chainComplex Struct r n c
  = ChainComplex $ toDgm r $ toBndOpr $ amap1 snd $ ccxSimplices n c where

  toBndOpr :: (Ring r, Commutative r, Ord r, Simplical s x)
    => FinList (n+1) (Set (s x)) -> FinList n (BoundaryOperator r s x)
  toBndOpr (_:|Nil) = Nil
  toBndOpr (sx:|sx':|sxs) = chors (Representable Boundary sx' sx) :| toBndOpr (sx':|sxs)

  -- converts to a Chain To diagram by possibly addapting the first operator to zero.
  toDgm :: (Ring r, Commutative r, Ord r, Simplical s x)
    => Regular
    -> FinList (n+1) (BoundaryOperator r s x)
    -> Diagram (Chain To) (n+2) (n+1) (BoundaryOperator r s x)
  toDgm r (d:|ds) = DiagramChainTo (end d') (d':|ds) where
    d' = case r of
      Regular   -> d              -- no addaption
      Truncated -> zeroEmptyEnd d -- to zero with empty end, but same start

  zeroEmptyEnd :: (Ring r, Commutative r, Ord r, Simplical s x)
    => BoundaryOperator r s x -> BoundaryOperator r s x
  zeroEmptyEnd d = zero (start d,empty) 

{-
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


-}
