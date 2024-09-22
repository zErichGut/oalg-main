
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : definition of a homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Homology'.
module OAlg.Homology.Definition
  (

    -- * Homology
    Homology(..)
  , hmgChainSet''
  , hmgChainSet'
  , hmgChainSet'MinusOne
  , hmgChainSet
  , hmgVariance
  , SomeHomology(..)

    -- ** Chain Homology
  , ChainHomology(..), chHomology
  , homology

    -- * Cycle
  , hmgCycleGenSet, hmgCycleGenSetMinusOne
  , hmgGroupGenSet, hmgGroupGenSetMinusOne

    -- * Boundary
  , hmgBoundary
  
    -- * Group
  , homologyGroup, homologyGroupMinusOne, homologyGroups

    -- * Class
  , homologyClass
  , HomologyClass

    -- * Failure
  , HomologyFailure(..)
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Either

import OAlg.Structure.Additive
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.FinList as F hiding ((++)) 
import OAlg.Entity.Matrix hiding (Transformation(..))
import OAlg.Entity.Slice

import OAlg.Entity.Sequence.Set

import OAlg.Entity.Diagram

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain as C
import OAlg.Homology.Simplex
import OAlg.Homology.Variance


-- import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- Homology -

data Homology n k x where
  Homology
    :: (Attestable n, Attestable k)
    => Any n
    -> Any k
    -> ChainComplex From N0 (BoundaryOperator Z x) -- ^ boundary operator
    -> Variance Free AbHom -- ^ variance of the boundary operator
    -> Homology n k x

--------------------------------------------------------------------------------
-- hmgVariance -

-- | the underlying 'Variance'.
hmgVariance :: Homology n k x -> Variance Free AbHom
hmgVariance (Homology _ _ _ v) = v

--------------------------------------------------------------------------------
-- hmgVarianceMinusOne -

-- | the induce 'Variance' for chains of length 0.
hmgVarianceMinusOne :: Homology n N0 k -> Variance Free AbHom
hmgVarianceMinusOne (Homology _ _ _ v) = ccxVarianceZ $ ccMinusOne v where
  ccMinusOne (Variance d3x3 _ _ _ _) = ChainComplex $ DiagramChainFrom (start c') (c':|z:|Nil) where
    DiagramChainFrom _ (_:|c:|Nil) = head $ dgPoints d3x3
    c' = abhz c
    z  = zero (end c' :> one ())
    
--------------------------------------------------------------------------------
-- hmgChainSet -

ssAny :: Attestable l => Set (Simplex l x) -> Any l
ssAny _ = attest

-- | the underlying set of @__k__@-simplices.
hmgChainSet :: (Entity x, Ord x) => Homology n k x -> Set (Simplex k x)
hmgChainSet (Homology _ k (ChainComplex ds) _) = case dgPoints ds of
  _:|_:|SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> s
    Nothing -> throw $ ImplementationError "invalid homology"
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe (k :~: l)
    eqAny _ _ = eqT

-- | the underlying set of @__k__ + 1@-simplices, generating the free abelian group of the
-- @__k__@ chain group.
hmgChainSet' :: (Entity x, Ord x) => Homology n k x -> Set (Simplex (k+1) x)
hmgChainSet' (Homology _ k (ChainComplex ds) _) = case dgPoints ds of
  _:|SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> s
    Nothing   -> throw $ ImplementationError "invalid homology"
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe ((k + 1) :~: l)
    eqAny _ _ = eqT

-- | the underlying set of @__0__@ simplices, generating the free abelian group of the
-- @__k__ - 1@ chain group.
hmgChainSet'MinusOne :: (Entity x, Ord x) => Homology n N0 x -> Set (Simplex N0 x)
hmgChainSet'MinusOne = hmgChainSet
{-
hmgChainSet'MinusOne h
  | s == one () = setEmpty
  | otherwise   = hmgChainSet h
  where
    Variance d3x3 _ _ _ _ = hmgVarianceMinusOne h
    DiagramChainFrom _ (d:|_) = head $ dgPoints d3x3
    s = end d
-}  

-- | the underlying set of @__k__ + 2@-simplices.
hmgChainSet'' :: (Entity x, Ord x) => Homology n k x -> Set (Simplex (k + 2) x)
hmgChainSet''  (Homology _ k (ChainComplex ds) _) = case dgPoints ds of
  SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> s
    Nothing -> throw $ ImplementationError "invalid homology"
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe ((k + 2) :~: l)
    eqAny _ _ = eqT

--------------------------------------------------------------------------------
-- homologyGroup -

-- | the homology group.
homologyGroup :: Homology n k x -> AbGroup
homologyGroup = vrcT' . hmgVariance

--------------------------------------------------------------------------------
-- hmgMinusOne -

homologyGroupMinusOne :: Homology n N0 x -> AbGroup
homologyGroupMinusOne = vrcT' . hmgVarianceMinusOne

--------------------------------------------------------------------------------
-- hmgCycleGenSet -

-- | a set of generators for the @__k__ + 1@-cycles.
hmgCycleGenSet :: (Entity x, Ord x) => Homology n k x -> Set (C.Chain Z (k+1) x)
hmgCycleGenSet h@(Homology _ _ _ v) = set $ amap1 (cfsssy s . abhvecFree1) $ setxs gs where
  s  = hmgChainSet' h
  gs = vrcCyclesGen v abgFinPres abhSplitable

--------------------------------------------------------------------------------
-- hmgCycleGenSetMinusOne -

hmgCycleGenSetMinusOne :: (Entity x, Ord x) => Homology n N0 x -> Set (C.Chain Z N0 x)
hmgCycleGenSetMinusOne h = set $ amap1 (cfsssy s . abhvecFree1) $ setxs gs where
  s  = hmgChainSet'MinusOne h
  v  = hmgVarianceMinusOne h
  gs = vrcCyclesGen v abgFinPres abhSplitable

--------------------------------------------------------------------------------
-- hmgGroupGenSet -

-- | a set of @__k__ + 1@-cycles, generating the homology group via 'homologyClass'.
hmgGroupGenSet :: (Entity x, Ord x) => Homology n k x -> Set (C.Chain Z (k+1) x)
hmgGroupGenSet h@(Homology _ _ _ v) = set $ amap1 (cfsssy s . abhvecFree1) $ setxs gs where
  s  = hmgChainSet' h
  gs = vrcHomologyGroupGen v abgFinPres abhSplitable

--------------------------------------------------------------------------------
-- hmgGroupGenSetMinusOne -

hmgGroupGenSetMinusOne :: (Entity x, Ord x) => Homology n N0 x -> Set (C.Chain Z N0 x)
hmgGroupGenSetMinusOne h = set $ amap1 (cfsssy s . abhvecFree1) $ setxs gs where
  s  = hmgChainSet'MinusOne h
  v  = hmgVarianceMinusOne h
  gs = vrcHomologyGroupGen v abgFinPres abhSplitable

--------------------------------------------------------------------------------
-- SomeHomology -

-- | some 'Homology'.
data SomeHomology n x where
  SomeHomology :: Homology n k x -> SomeHomology n x

--------------------------------------------------------------------------------
-- ChainHomology -

-- | a finite list @s __n__ __n__, s __n__ (__n__-1) .. s __n__ __0__@ of 'SomeHomology' where
--   @s ___n__ __k__@ contains a homology in @'Homology' __n__ __k__ x@.
newtype ChainHomology n x = ChainHomology (FinList (n+1) (SomeHomology n x))

--------------------------------------------------------------------------------
-- chHomology -

-- | gets the homology of @'Homology' __n__ __k__ __x__@.
chHomology :: Attestable k => Any k -> ChainHomology n x -> Homology n k x
chHomology k (ChainHomology hs) = chh k hs where
  chh :: Attestable k => Any k -> FinList l (SomeHomology n x) -> Homology n k x
  chh _ Nil                   = throw $ InvalidData "chHomology: ChainHomology"
  chh k (SomeHomology h:|shs) = case eqAny k h of
    Just Refl -> h
    Nothing   -> chh k shs
    
    where eqAny :: Attestable k => Any k -> Homology n k' x -> Maybe (k :~: k')
          eqAny _ (Homology _ _ _ _) = eqT

--------------------------------------------------------------------------------
-- homology -

-- | the 'ChainHomology'.
homology :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> ChainHomology n x
homology r c = ChainHomology hs where
  hs = amap1 (uncurry $ shmg $ cpxDim c) ((ccxMap' ccxHead ds) `zip` (ccxMap' ccxVarianceZ vs))
  
  ds = chainComplex r c
  vs = ccxMap HomBoundaryOperator ds

  shmg :: (Entity x, Ord x, Attestable n)
       => Any n
       -> ChainComplex From N0 (BoundaryOperator Z x)
       -> Variance Free AbHom
       -> SomeHomology n x
  shmg n d v = case bdoDim d of
    SomeNatural k -> SomeHomology $ Homology n k d v

--------------------------------------------------------------------------------
-- HomologyFailure -

data HomologyFailure r k h x
  = -- | the representable part, if the given chain is not representable in the underlying simplex set.
    NotRepresentable (C.Chain r (k+1) x)
    
    -- | the boundary, if the given chain is not a cycle..
  | NotACycle (C.Chain r k x)

    -- | the homology class, it the given chain has no boundary.
  | NonTrivialHomologyClass h
  deriving (Show)

--------------------------------------------------------------------------------
-- HomologyClass -

type HomologyClass = AbElement

--------------------------------------------------------------------------------
-- homologyGroups -

-- | the homology groups starting by @__n__@ to @__0__@.
homologyGroups :: ChainHomology n x -> FinList (n+1) AbGroup
homologyGroups (ChainHomology hs) = amap1 hg hs where
  hg (SomeHomology h) = homologyGroup h


--------------------------------------------------------------------------------
-- homologyClass -

-- | the homology class of a given chain according to the given homology.
homologyClass :: (Entity x, Ord x)
  => Homology n k x
  -> C.Chain Z (k+1) x
  -> Either (HomologyFailure Z k AbElement x) AbElement
homologyClass h@(Homology _ _ _ v) s
  | not (isZero (s - s')) = Left (NotRepresentable s')
  | otherwise = case vrcHomologyClass v (vecabhFree1 (lengthN ss') sv) of
      Left t -> Left $ NotACycle $ cfsssy (hmgChainSet h) $ abhvecFree1 t
      Right t' -> Right $ AbElement t'
  where 
    ss' = hmgChainSet' h
    sv  = ssycfs ss' s
    s'  = cfsssy ss' sv

--------------------------------------------------------------------------------
-- hmgBoundary -

-- | evaluates a boundary for the given chain @s@ according to the given homology @h@,
-- i.e. a @h@-representable element @d@ in @'C.Chain' 'Z' (__k__ + 2) __x__@ such that
-- @'boundary' d '==' s@. If no such @d@ exists, than the result will be a 'HomologyFailure' where
--
-- (1) If @s@ is not @h@-representable, then the result will be @'NotRepresentable' s'@ where @s'@ is
-- the @h@-representable part of @s@.
--
-- (2) If @s@ is not a cycle, then the result will be @'NotACycle' ('boundary' s)@.
--
-- (3) If the homology class of @s@ is not zero, then the result will be
-- @'NonTrivialHomologyClass' ('homologyClass' s)@.
hmgBoundary :: (Entity x, Ord x)
  => Homology n k x
  -> C.Chain Z (k+1) x
  -> Either (HomologyFailure Z k AbElement x) (C.Chain Z (k+2) x)
hmgBoundary h@(Homology _ _ _ v) s
  | not (isZero (s - s')) = Left (NotRepresentable s')
  | otherwise = case vrcBoundary v (vecabhFree1 (lengthN ss') sv) of
      Left (Left t)   -> Left $ NotACycle $ cfsssy (hmgChainSet h) $ abhvecFree1 t
      Left (Right t') -> Left $ NonTrivialHomologyClass $ AbElement t'
      Right r         -> Right $ cfsssy (hmgChainSet'' h) $ abhvecFree1 r
  where
    ss' = hmgChainSet' h
    sv  = ssycfs ss' s
    s'  = cfsssy ss' sv

{-
c = complex kleinBottle
ht = homology Truncated $ c
hr = homology Regular c
ht0 = chHomology (attest :: Any N0) ht
hr0 = chHomology (attest :: Any N0) hr
ht1 = chHomology (attest :: Any N1) ht
hr1 = chHomology (attest :: Any N1) hr
v s = ch (Simplex (s:|Nil)) :: Chain Z N1 Symbol
-}
