
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, DeriveAnyClass #-}
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
  , ccxhDomain, ccxhRange
  , ChainComplexHom(..)
  , MapOperator
  , ccxhOne, ccxhMlt
  , ccxhZero, ccxhAdd
  , ccxhNegate, ccxhSbtr
  , ccxhSclMlt

    -- ** Representaiton
  , ccxRepMatrixHom, ccxCardsHom

    -- * Some Chain Complex
  , SomeChainComplex(..)
  , SomeChainComplexHom(..)
  , eqVertexType

  ) where

import Data.Typeable
import Data.List as L (repeat,(++),zip) 

import OAlg.Prelude

import OAlg.Category.Map

import OAlg.Data.Filterable

import OAlg.Structure.Exception
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Vectorial
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

instance Validable (ChainComplexType t) where
  valid ChainComplexStandard = SValid
  valid ChainComplexExtended = SValid

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

instance (AlgebraicSemiring r, Ring r, Ord r, Simplical s x)
  => Validable (ChainComplex t r s n x) where
  valid (ChainComplex t d) = Label "ChainComplex" :<=>:
    And [ valid t
        , valid d
        , Label "ChainComplexType" :<=>: vldCcxType t d
        ] where

    vldCcxType ::
      (AlgebraicSemiring r, Ring r, Ord r, Simplical s x)
      => ChainComplexType t -> Diagram (Chain To) (n+2) (n+1) (BoundaryOperator r s x)
      -> Statement
    vldCcxType t (DiagramChainTo _ (d0:|_)) = case t of
      ChainComplexStandard -> isZero d0 :?> Params ["d0":=show d0]
      ChainComplexExtended -> SValid
    
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

instance (Ring r, Ord r, AlgebraicSemiring r, Simplical s x, Simplical s y)
  => Validable (ChainComplexHom t r s n x y) where
  valid (ChainComplexHom a b fs) = Label "ChainComplexHom" :<=>:
    And [ valid a
        , valid b
        , valid fs
        , Label "commutative" :<=>: vldCom 0 (dgArrows $ ccxDiagram a) (dgArrows $ ccxDiagram b) fs
        ] where

    vldCom ::
      (Ring r, Ord r, AlgebraicSemiring r, Simplical s x, Simplical s y)
      => N
      -> FinList n (BoundaryOperator r s x) -> FinList n (BoundaryOperator r s y)
      -> FinList (n+1) (MapOperator r s x y)
      -> Statement
    vldCom _ Nil _ _ = SValid
    vldCom i (d:|ds) (d':|ds') (f:|f':|fs)
      = And [ (chorsMlt f d == chorsMlt d' f') :?> Params ["i":=show i]
            , vldCom (succ i) ds ds' (f':|fs)
            ]

--------------------------------------------------------------------------------
-- ccxhDomain -

ccxhDomain :: ChainComplexHom t r s n x y -> ChainComplex t r s n x
ccxhDomain (ChainComplexHom d _ _) = d

--------------------------------------------------------------------------------
-- ccxhRange -

ccxhRange :: ChainComplexHom t r s n x y -> ChainComplex t r s n y
ccxhRange (ChainComplexHom _ r _) = r

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
-- ccxhOne -

ccxhOne :: (Ring r, Ord r, AlgebraicSemiring r, Simplical s x)
  => ChainComplex t r s n x -> ChainComplexHom t r s n x x
ccxhOne c = ChainComplexHom c c (amap1 chorsOne $ dgPoints $ ccxDiagram c)

--------------------------------------------------------------------------------
-- ccxhMlt -

ccxhMlt ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y, Simplical s z)
  => ChainComplexHom t r s n y z -> ChainComplexHom t r s n x y
  -> ChainComplexHom t r s n x z
ccxhMlt (ChainComplexHom b' c fs) (ChainComplexHom a b gs)
  | b' /= b   = throw NotMultiplicable
  | otherwise = ChainComplexHom a c (amap1 (uncurry chorsMlt) (fs `F.zip` gs))

--------------------------------------------------------------------------------
-- ccxhZero -

ccxhZero ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => ChainComplex t r s n x -> ChainComplex t r s n y
  -> ChainComplexHom t r s n x y
ccxhZero a b
  = ChainComplexHom a b (amap1 zero $ ((dgPoints $ ccxDiagram a) `F.zip` (dgPoints $ ccxDiagram b)))

--------------------------------------------------------------------------------
-- ccxhAdd -

ccxhAdd ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => ChainComplexHom t r s n x y -> ChainComplexHom t r s n x y
  -> ChainComplexHom t r s n x y
ccxhAdd (ChainComplexHom a b fs) (ChainComplexHom a' b' gs)
  | (a,b) /= (a',b') = throw NotAddable
  | otherwise        = ChainComplexHom a b (amap1 (uncurry (+)) (fs `F.zip` gs))

--------------------------------------------------------------------------------
-- ccxhNegate -

ccxhNegate ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => ChainComplexHom t r s n x y -> ChainComplexHom t r s n x y
ccxhNegate (ChainComplexHom a b fs) = ChainComplexHom a b (amap1 negate fs)

--------------------------------------------------------------------------------
-- ccxhSbtr -

ccxhSbtr ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => ChainComplexHom t r s n x y -> ChainComplexHom t r s n x y
  -> ChainComplexHom t r s n x y
ccxhSbtr (ChainComplexHom a b fs) (ChainComplexHom a' b' gs)
  | (a,b) /= (a',b') = throw NotAddable
  | otherwise        = ChainComplexHom a b (amap1 (uncurry (-)) $ (fs `F.zip` gs))

--------------------------------------------------------------------------------
-- ccxhSclMlt -

ccxhSclMlt ::
  (Ring r, Commutative r, Ord r, Simplical s x, Simplical s y)
  => r -> ChainComplexHom t r s n x y -> ChainComplexHom t r s n x y
ccxhSclMlt r (ChainComplexHom a b fs) = ChainComplexHom a b (amap1 (r!) fs)

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

--------------------------------------------------------------------------------
-- eqVertexType -

eqVertexType :: (Typeable x, Typeable y) => c x -> c y -> Maybe (x :~: y)
eqVertexType _ _ = eqT

--------------------------------------------------------------------------------
-- SomeChainComplex -

data SomeChainComplex t r s n where
  SomeChainComplex :: (Simplical s x, Attestable n)
    => ChainComplex t r s n x -> SomeChainComplex t r s n

deriving instance (Ring r, Commutative r, Ord r) => Show (SomeChainComplex t r s n)

instance (Ring r, Commutative r, Ord r) => Eq (SomeChainComplex t r s n) where
  SomeChainComplex a == SomeChainComplex b = case eqVertexType a b of
    Just Refl -> a == b
    Nothing   -> False

instance (AlgebraicSemiring r, Ring r, Ord r) => Validable (SomeChainComplex t r s n) where
  valid (SomeChainComplex c) = Label "SomeChainComplex" :<=>: valid c

--------------------------------------------------------------------------------
-- SomeChainChomplexHom -

data SomeChainComplexHom t r n where
  SomeChainComplexHom :: (Entity x, Ord x, Entity y, Ord y)
    => ChainComplexHom t r Asc n x y -> SomeChainComplexHom t r n

deriving instance (Ring r, Ord r, AlgebraicSemiring r) => Show (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r) => Eq (SomeChainComplexHom t r n) where
  SomeChainComplexHom f == SomeChainComplexHom g
    = case (eqVertexType (ccxhDomain f) (ccxhDomain g),eqVertexType (ccxhRange f) (ccxhRange g)) of
        (Just Refl,Just Refl) -> f == g
        _                     -> False

instance (Ring r, Ord r, AlgebraicSemiring r) => Validable (SomeChainComplexHom t r n) where
  valid (SomeChainComplexHom f) = Label "SomeChainComplexHom" :<=>: valid f

--------------------------------------------------------------------------------
-- SomeChainComplexHom - Multiplicative -

type instance Point (SomeChainComplexHom t r n) = SomeChainComplex t r Asc n

deriving instance (Ring r, Commutative r, Ord r) => ShowPoint (SomeChainComplexHom t r n)
deriving instance (Ring r, Commutative r, Ord r) => EqPoint (SomeChainComplexHom t r n)
deriving instance (AlgebraicSemiring r, Ring r, Ord r) => ValidablePoint (SomeChainComplexHom t r n)
deriving instance (Typeable t, Typeable r, Typeable n) => TypeablePoint (SomeChainComplexHom t r n)


instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Oriented (SomeChainComplexHom t r n) where
  start (SomeChainComplexHom f) = SomeChainComplex $ ccxhDomain f
  end (SomeChainComplexHom f)   = SomeChainComplex $ ccxhRange f

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Multiplicative (SomeChainComplexHom t r n) where
  one (SomeChainComplex c) = SomeChainComplexHom $ ccxhOne c

  SomeChainComplexHom f * SomeChainComplexHom g
    = case eqVertexType (ccxhRange g) (ccxhDomain f) of
        Just Refl -> SomeChainComplexHom (f `ccxhMlt` g)
        Nothing   -> throw NotMultiplicable

type instance Root (SomeChainComplexHom t r n) = Orientation (SomeChainComplex t r Asc n)

deriving instance (Ring r,Commutative r, Ord r) => ShowRoot (SomeChainComplexHom t r n)
deriving instance (Ring r,Commutative r, Ord r) => EqRoot (SomeChainComplexHom t r n)
deriving instance (AlgebraicSemiring r, Ring r, Ord r) => ValidableRoot (SomeChainComplexHom t r n)
deriving instance (Typeable r, Typeable t, Typeable n) => TypeableRoot (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Fibred (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Additive (SomeChainComplexHom t r n) where
  zero (SomeChainComplex a :> SomeChainComplex b)
    = SomeChainComplexHom $ ccxhZero a b

  SomeChainComplexHom f + SomeChainComplexHom g
    = case (eqVertexType (ccxhDomain f) (ccxhDomain g),eqVertexType (ccxhRange f) (ccxhRange g)) of
        (Just Refl,Just Refl) -> SomeChainComplexHom (f `ccxhAdd` g)
        _                     -> throw NotAddable

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Abelian (SomeChainComplexHom t r n) where
  negate (SomeChainComplexHom f) = SomeChainComplexHom $ ccxhNegate f

  SomeChainComplexHom f - SomeChainComplexHom g
    = case (eqVertexType (ccxhDomain f) (ccxhDomain g),eqVertexType (ccxhRange f) (ccxhRange g)) of
        (Just Refl,Just Refl) -> SomeChainComplexHom $ ccxhSbtr f g
        _                     -> throw NotAddable

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Vectorial (SomeChainComplexHom t r n) where
  type Scalar (SomeChainComplexHom t r n) = r
  r ! (SomeChainComplexHom f) = SomeChainComplexHom (r `ccxhSclMlt` f)

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => FibredOriented (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Distributive (SomeChainComplexHom t r n)

instance (Ring r, Ord r, AlgebraicSemiring r, Typeable t, Attestable n)
  => Algebraic (SomeChainComplexHom t r n)
