
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , RankNTypes
#-}

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
    ChainComplex(..), chainComplex

    -- ** Representation
  , ChainComplexRep(..), chainComplexRep, Regular(..)

    -- * Transformation
  , ChainComplexTrafo(..)
  , chainComplexTrafo

    -- ** Representation
  , ChainComplexTrafoRep(..), cctDomainRep, cctRangeRep
  , chainComplexTrafoRep

  ) where

import Control.Monad

import Data.Kind
import Data.Typeable
import Data.Foldable (toList)
import Data.List as L (head,tail,repeat,(++),zip) 

import OAlg.Prelude hiding (T,empty)

import OAlg.Category.Map

import OAlg.Data.Filterable
import OAlg.Data.Singleton

import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Exponential

import OAlg.Entity.Diagram as D
import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Matrix hiding (Transformation(..))

import OAlg.Limes.Exact.ConsZero

import OAlg.Hom.Definition

import OAlg.Homology.Complex
import OAlg.Homology.Chain as C
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
-- ccxBoundary -

-- | the list of boundary operators, where in the 'Regualr' case the first operator
-- is addapted to @'ZeroHom' s 'empty'@.
ccxBoundary :: Simplical s x => Regular -> Any n -> Complex x
  -> FinList (n+2) (ChainHom r s (C.Chain r s x) (C.Chain r s x)) 
ccxBoundary r n c = case r of
  Regular  -> zeroBnd (F.head ds) :| F.tail ds
  Extended -> ds
  where
    ds = toBnd $ ccxSimplices n c

    zeroBnd :: ChainHom r s (C.Chain r s x) (C.Chain r s x)
      -> ChainHom r s (C.Chain r s x) (C.Chain r s x)
    zeroBnd (Boundary s _) = ZeroHom s empty
    zeroBnd _              = throw $ ImplementationError "ccxBoundary.zeroBnd"
    
    toBnd :: Simplical s x
      => FinList (n+1) (Z,Set (s x)) -> FinList n (ChainHom r s (C.Chain r s x) (C.Chain r s x))
    toBnd (_:|Nil) = Nil
    toBnd (zs:|zs':|zss) = Boundary (snd zs') (snd zs) :| toBnd (zs':|zss)

ccxBoundaryAscZ :: (s ~  Asc, Entity x, Ord x)
  => Regular -> Any n -> Complex x -> FinList (n+2) (ChainHom Z s (C.Chain Z s x) (C.Chain Z s x))
ccxBoundaryAscZ = ccxBoundary


--------------------------------------------------------------------------------
-- ccxChainMap -

ccxChainMap :: Homological s x y
  => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> FinList (n+3) (ChainHom r s (C.Chain r s x) (C.Chain r s y))
ccxChainMap r n f = case r of
  Regular  -> zeroChnMap (F.head fs) :| F.tail fs
  Extended -> fs
  where

    fs = toChnMap (cpmMap f) (ccxSimplices n $ cpmDomain f) (ccxSimplices n $ cpmRange f)

    zeroChnMap :: ChainHom r s (C.Chain r s x) (C.Chain r s y)
      -> ChainHom r s (C.Chain r s x) (C.Chain r s y)
    zeroChnMap (ChainMap _ _ _) = ZeroHom empty empty
    zeroChnMap _                = throw $ ImplementationError "ccxChainMap.zeroChnMap"
    
    toChnMap :: SimplicalTransformable s x y
      => Map EntOrd x y -> FinList n (Z,Set (s x)) -> FinList n (Z,Set (s y))
      -> FinList n (ChainHom r s (C.Chain r s x) (C.Chain r s y))
    toChnMap _ Nil Nil                 = Nil
    toChnMap f (zsx:|zsxs) (zsy:|zsys) = ChainMap (snd zsx) (snd zsy) f :| toChnMap f zsxs zsys

ccxChainMapZ :: Homological s x y
  => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> FinList (n+3) (ChainHom Z s (C.Chain Z s x) (C.Chain Z s y))
ccxChainMapZ = ccxChainMap

--------------------------------------------------------------------------------
-- ChainComplex -

-- | chain complex.
type ChainComplex = ConsZero To

--------------------------------------------------------------------------------
-- ChainComplexRep --

-- | predicate for being a list of eligible boundary operators.
--
--  __Properties__ Let @c = 'ChainComplexRep' ds@ be in @'ChainComplexRep' __r__ __s__ __n__ __x__@,
-- where @__r__@ is a 'Commutative' 'Ring', then holds:
--
-- (1) For all @..d'|'d'..@ in @ds@ holds: @'chDomainSet' d '==' 'chRangeSet' d'@.
--
-- (2) Let @d = 'F.head' c@, then holds:
--
--     (2.1) If @d@ matches @'ZeroHom' _ s0@ then @s0@ is 'empty'. (for the 'Regualr' case)
--
--     (2.2) If @d@ matches @'Boundary' _ _@ then @d@ is 'valid'.
--
--     (2.3) otherwise @d@ is not 'valid'.
--
-- (3) Let @d@ be in @'F.tail' ds@, then holds:
--
--     (3.1) If @d@ matches @'Boundary' _ _@ then @d@ is 'valid'.
--
--     (3.2) otherwise @d@ is not 'valid'.
newtype ChainComplexRep r s n x
  = ChainComplexRep (FinList (n+2) (ChainHom r s (C.Chain r s x) (C.Chain r s x)))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ChainComplexRep - Validable -

instance (Ring r, Commutative r, Simplical s x) => Validable (ChainComplexRep r s n x) where
  valid (ChainComplexRep ds) = Label "ChainComplexRep" :<=>:
    And [ vldBnd0 d0
        , vldBnds 0 d0 (F.tail ds)
        ]
    where
      d0 = F.head ds
      
      vldBnd0 d = And [ valid d
                      , case d of
                          ZeroHom _ s0 -> Label "2.1" :<=>: isEmpty s0 :?> Params ["s0":=show s0]
                          Boundary _ _ -> SValid
                          _            -> Label "2.3" :<=>: SInvalid
                      ]
                  
      vldBnd d = And [ valid d
                      , case d of
                         Boundary _ _ -> SValid
                         _            -> Label "3.2" :<=>: SInvalid
                     ]

      vldBnds :: Simplical s x
        => N
        -> ChainHom r s (C.Chain r s x) (C.Chain r s x)
        -> FinList (n+1) (ChainHom r s (C.Chain r s x) (C.Chain r s x))
        -> Statement
      vldBnds _ _ (d:|Nil) = vldBnd d
      vldBnds i d (d':|d'':|ds)
        = And [ vldBnd d'
              , Label "1" :<=>: (chDomainSet d == chRangeSet d') :?> Params ["i":=show i]
              , vldBnds (succ i) d' (d'':|ds)
              ]

--------------------------------------------------------------------------------
-- chainComplex -

-- | the underlying chain complex.
chainComplex :: (Ring r, Commutative r, Simplical s x)
  => ChainComplexRep r s n x -> ChainComplex n (Matrix r)
chainComplex (ChainComplexRep ds) = ConsZero (DiagramChainTo (end $ F.head ms) ms) where
  ms = amap1 (repMatrix . chainHomRep) ds


--------------------------------------------------------------------------------
-- chainComplexRep -

chainComplexRep :: Simplical s x
  => Regular -> Any n -> Complex x -> ChainComplexRep r s n x
chainComplexRep r n c = ChainComplexRep (ccxBoundary r n c)

ccxSetZ :: (r ~ Z, s ~ Set, Simplical s x) => Regular -> Any n -> Complex x -> ChainComplexRep r s n x
ccxSetZ = chainComplexRep

ccxLstZ :: (r ~ Z, s ~ [], Simplical s x) => Regular -> Any n -> Complex x -> ChainComplexRep r s n x
ccxLstZ = chainComplexRep

ccxAscZ :: (r ~ Z, s ~ Asc, Simplical s x) => Regular -> Any n -> Complex x -> ChainComplexRep r s n x
ccxAscZ = chainComplexRep

--------------------------------------------------------------------------------
-- ccxRepCards -

-- | the cardinalities of a the boundary operators.
ccxRepCards :: ChainComplexRep r s n x -> ChainComplexCards (n+3)
ccxRepCards (ChainComplexRep ds) = DiagramDiscrete (cs ds) where
  cs :: FinList (n+2) (ChainHom r s (C.Chain r s x) (C.Chain r s x)) -> FinList (n+3) N
  cs (d:|d':|Nil)
    = (lengthN $ chRangeSet d) :| (lengthN $ chRangeSet d') :| (lengthN $ chDomainSet d') :| Nil
  cs (d:|d':|d'':|ds) = (lengthN $ chRangeSet d) :| cs (d':|d'':|ds)

--------------------------------------------------------------------------------
-- ChainComplexTrafo -

-- | transformation between chain complexes.
type ChainComplexTrafo = ConsZeroTrafo To

--------------------------------------------------------------------------------
-- ChainComplexTrafoRep -

-- | predicate for beeing a list of eligible chain map operators.
--
--  __Property__ Let @r@ be in
--  @'ChainComplexTrafoRep' __r__ __s__ __n__ __x__ __y__@, where @__r__@ is a 'Commutative' 'Ringe',
--  then holds: The induced chain comples transformation @'chainComplexTrafo' r@ is 'valid'.
newtype ChainComplexTrafoRep r s n x y
  = ChainComplexTrafoRep
      (FinList (n+3) (ChainHom r s (C.Chain r s x) (C.Chain r s y)))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- cctDomainRep -

-- | the induced boundary operators according to the domain.
cctDomainRep :: Simplical s x
  => ChainComplexTrafoRep r s n x y -> ChainComplexRep r s n x
cctDomainRep (ChainComplexTrafoRep (f0:|f1:|fs)) = ChainComplexRep (d0 f0 f1:|ds (f1:|fs)) where
  d0 (ZeroHom s0 _) f1 = ZeroHom (chDomainSet f1) s0
  d0 f0 f1             = Boundary (chDomainSet f1) (chDomainSet f0)

  ds :: Simplical s x
    => FinList (n+1) (ChainHom r s (C.Chain r s x) (C.Chain r s y))
    -> FinList n (ChainHom r s (C.Chain r s x) (C.Chain r s x))
  ds (_:|Nil) = Nil
  ds (f:|f':|fs) = Boundary (chDomainSet f') (chDomainSet f) :| ds (f':|fs)

--------------------------------------------------------------------------------
-- cctRangeRep -

-- | the induced boundary operators according to the range.
cctRangeRep :: Simplical s y
  => ChainComplexTrafoRep r s n x y -> ChainComplexRep r s n y
cctRangeRep (ChainComplexTrafoRep (f0:|f1:|fs)) = ChainComplexRep (d0 f0 f1:|ds (f1:|fs)) where
  d0 (ZeroHom _ s0) f1 = ZeroHom (chRangeSet f1) s0
  d0 f0 f1             = Boundary (chRangeSet f1) (chRangeSet f0)

  ds :: Simplical s y
    => FinList (n+1) (ChainHom r s (C.Chain r s x) (C.Chain r s y))
    -> FinList n (ChainHom r s (C.Chain r s y) (C.Chain r s y))
  ds (_:|Nil) = Nil
  ds (f:|f':|fs) = Boundary (chRangeSet f') (chRangeSet f) :| ds (f':|fs)

--------------------------------------------------------------------------------
-- chainComplexTrafo -

-- | the induced transformation between chain complexes.
chainComplexTrafo :: (Ring r, Commutative r, Homological s x y)
  => ChainComplexTrafoRep r s n x y -> ChainComplexTrafo n (Matrix r)
chainComplexTrafo r@(ChainComplexTrafoRep fs) = ConsZeroTrafo dDom dRng ms where
  dDom = chainComplex $ cctDomainRep r
  dRng = chainComplex $ cctRangeRep r
  ms   = amap1 (repMatrix . chainHomRep) fs

--------------------------------------------------------------------------------
-- chainComplexTrafoRep -

chainComplexTrafoRep :: Homological s x y
  => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> ChainComplexTrafoRep r s n x y
chainComplexTrafoRep r n f = ChainComplexTrafoRep (ccxChainMap r n f)

chainComplexTrafoRepZ :: Homological s x y
  => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
  -> ChainComplexTrafoRep Z s n x y
chainComplexTrafoRepZ = chainComplexTrafoRep

a = complex [Set "abc"]
b = complex [Set [0,1]] :: Complex N

c = cpxProductAsc b a

p1 = ComplexMapAsc c b (Map fst)
p2 = ComplexMapAsc c a (Map snd)

c' = cpxProduct b a

p1' = ComplexMap c b (Map fst)
p2' = ComplexMap c a (Map snd)


