
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
{-
    -- * Homology
    Homology(..), hmlGroup
  , ccplHomology
-}

  ) where

import Data.Typeable

import Data.Foldable
import Data.List as L (filter,(++),zip)
import qualified Data.Map.Strict as M

import OAlg.Prelude

import OAlg.Data.Generator
import OAlg.Data.Constructable
import OAlg.Data.Either
import OAlg.Data.Tree

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial
import OAlg.Structure.Exception
import OAlg.Structure.Ring

import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.FinList as F hiding ((++)) 
import OAlg.Entity.Matrix hiding (Transformation(..))
import OAlg.Entity.Slice
import OAlg.Entity.Sum
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Diagram

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain as C
import OAlg.Homology.Simplex


import OAlg.Data.Symbol

{-
hmgCycles :: (Entity x, Ord x) => Homology n k x -> Set (C.Chain Z (k+1) x)
hmgCycles h@(Homology _ _ _ v)
  = set $ amap1 (cfsssy (hmgChainSet' h) . fromAbSlice) $ setxs $ vrcCycles $ v
-}

ssAny :: Attestable l => Set (Simplex l x) -> Any l
ssAny _ = attest

bdoSimplexSet' :: (Ring r, Commutative r, Ord r, OrdPoint r, Entity x, Ord x, Attestable k)
  => Any k -> ChainComplex From n (BoundaryOperator r x) -> Maybe (Set (Simplex (k+1) x))
bdoSimplexSet' k (ChainComplex ds) = case dgPoints ds of
  _:|SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> Just s
    Nothing   -> Nothing
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe ((k + 1) :~: l)
    eqAny _ _ = eqT
 
--------------------------------------------------------------------------------
-- Homology -

type CyGens k x = M.Map N (C.Chain Z k x) 

data Homology n k x where
  Homology
    :: (Attestable n, Attestable k)
    => Any n
    -> Any k
    -> ChainComplex From N0 (BoundaryOperator Z x) -- ^ boundary operator
    -> Variance Free AbHom -- ^ variance of the boundary operator
    -> CyGens (k+1) x -- ^ set of generators for thy cycles
    -> Homology n k x

--------------------------------------------------------------------------------
-- hmgVariance -

hmgVariance :: Homology n k x -> Variance Free AbHom
hmgVariance (Homology _ _ _ v _) = v


--------------------------------------------------------------------------------
-- hmgGroup -

hmgGroup :: Homology n k x -> AbGroup
hmgGroup = vrcT' . hmgVariance

--------------------------------------------------------------------------------
-- hmgCyGens -

hmgCyGens :: (Entity x, Ord x) => Homology n k x -> CyGens (k+1) x
hmgCyGens (Homology _ _ _ _ cs) = cs

--------------------------------------------------------------------------------
-- hmgCycles -

-- | a set of generators for the cycles.
hmgCycles :: (Entity x, Ord x) => Homology n k x -> Set (C.Chain Z (k+1) x)
hmgCycles = Set . M.elems . hmgCyGens

--------------------------------------------------------------------------------
-- hmgCyclesCard -

-- | cardinality of the underlying set of generators for the cycles.
hmgCyclesCard :: (Entity x, Ord x) => Homology n k x -> N
hmgCyclesCard = toEnum . M.size . hmgCyGens

--------------------------------------------------------------------------------
-- hmgCycle -

-- | the @i@-the cycle of the underlying set of generators for the cycles.
hmgCycle :: (Entity x, Ord x) => Homology n k x -> N -> C.Chain Z (k+1) x
hmgCycle  = (M.!) . hmgCyGens

--------------------------------------------------------------------------------
-- SomeHomology -

data SomeHomology n x where
  SomeHomology :: Homology n k x -> SomeHomology n x

getHomology :: Attestable k => Any k -> FinList l (SomeHomology n x) -> Maybe (Homology n k x)
getHomology _ Nil                   = Nothing
getHomology k (SomeHomology h:|shs) = case eqAny k h of
  Just Refl -> Just h
  Nothing   -> getHomology k shs
  
  where eqAny :: Attestable k => Any k -> Homology n k' x -> Maybe (k :~: k')
        eqAny _ (Homology _ _ _ _ _) = eqT

--------------------------------------------------------------------------------
-- homology -

homology :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> FinList (n+1) (SomeHomology n x)
homology r c
  = amap1 (uncurry $ shmg $ cpxDim c) ((ccxMap' ccxHead ds) `F.zip` (ccxMap' ccxVarianceZ vs)) where
  
  ds = chainComplex r c
  vs = ccxMap HomBoundaryOperator ds

  shmg :: (Entity x, Ord x, Attestable n)
       => Any n
       -> ChainComplex From N0 (BoundaryOperator Z x)
       -> Variance Free AbHom
       -> SomeHomology n x
  shmg n d v = case bdoDim d of
    SomeNatural k -> SomeHomology $ Homology n k d v cGen where
      cGen = case bdoSimplexSet' k d of
        Just s -> M.fromAscList ([0..] `L.zip` cs) where
          cas    = vrcCycles v abgFinPres abhSplitable
          Set cs = set $ amap1 (cfsssy s . fromAbSlice) $ setxs cas
        Nothing -> throw $ ImplementationError "homology cGen"

--------------------------------------------------------------------------------
-- HomologyClass -

type HomologyClass = AbElement

--------------------------------------------------------------------------------
-- hmgChainSet -


hmgChainSet :: (Entity x, Ord x, Attestable k) => Homology n k x -> Set (Simplex k x)
hmgChainSet (Homology _ k (ChainComplex ds) _ _) = case dgPoints ds of
  _:|_:|SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> s
    Nothing -> throw $ ImplementationError "invalid homology"
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe (k :~: l)
    eqAny _ _ = eqT


hmgChainSet' :: (Entity x, Ord x, Attestable k) => Homology n k x -> Set (Simplex (k+1) x)
hmgChainSet' (Homology _ k ds _ _) = case bdoSimplexSet' k ds of
  Just s  -> s
  Nothing -> throw $ ImplementationError "invalid homology"

hmgChainSet'' :: (Entity x, Ord x, Attestable k) => Homology n k x -> Set (Simplex (k + 2) x)
hmgChainSet''  (Homology _ k (ChainComplex ds) _ _) = case dgPoints ds of
  SimplexSet s:|_  -> case eqAny k (ssAny s) of
    Just Refl -> s
    Nothing -> throw $ ImplementationError "invalid homology"
  where
    eqAny :: (Attestable k, Attestable l) => Any k -> Any l -> Maybe ((k + 2) :~: l)
    eqAny _ _ = eqT


--------------------------------------------------------------------------------
-- HomologyFailure -


data HomologyFailure r k h x
  = NotRepresentable (C.Chain r (k+1) x) -- ^ the representable part, if the given chain is not representable in the underlying simplex set.
  | NotACycle (C.Chain r k x) -- ^ the boundary, if the given chain is not a cycle..
  | NonTrivialHomologyClass h -- ^ the homology class, it the given chain has no boundary.
  deriving (Show)

--------------------------------------------------------------------------------
-- toAbSlice -

toAbSlice :: N -> Vector Z -> Slice From (Free N1) AbHom
toAbSlice r v = SliceFrom (Free attest :: Free N1 AbHom) (zabh h) where
  h = matrixTtl r 1 $ amap1 (\(x,i) -> (x,i,0)) $ filter ((<r).snd) $ psqxs $ vecpsq v 

--------------------------------------------------------------------------------
-- fromAbSlice -

fromAbSlice :: Slice From (Free N1) AbHom -> Vector Z
fromAbSlice (SliceFrom _ h) = fstRow $ mtxRowCol $ abhz h where
  fstRow :: (i ~ N, j ~ N) => Row j (Col i r) -> Vector r
  fstRow (Row (PSequence rs)) = case rs of
    []            -> Vector psqEmpty
    [(Col ris,0)] -> Vector ris
    _             -> throw $ InvalidData "fromAbSlice"
    
--------------------------------------------------------------------------------
-- homologyClass -

homologyClass :: (Entity x, Ord x)
  => Homology n k x
  -> C.Chain Z (k+1) x
  -> Either (HomologyFailure Z k AbElement x) AbElement
homologyClass h@(Homology _ _ _ v _) s
  | not (isZero (s - s')) = Left (NotRepresentable s')
  | otherwise = case vrcHomologyClass v (toAbSlice (lengthN ss') sv) of
      Left t -> Left $ NotACycle $ cfsssy (hmgChainSet h) $ fromAbSlice t
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
hmgBoundary h@(Homology _ _ _ v _) s
  | not (isZero (s - s')) = Left (NotRepresentable s')
  | otherwise = case vrcBoundary v (toAbSlice (lengthN ss') sv) of
      Left (Left t)   -> Left $ NotACycle $ cfsssy (hmgChainSet h) $ fromAbSlice t
      Left (Right t') -> Left $ NonTrivialHomologyClass $ AbElement t'
      Right r         -> Right $ cfsssy (hmgChainSet'' h) $ fromAbSlice r
  where
    ss' = hmgChainSet' h
    sv  = ssycfs ss' s
    s'  = cfsssy ss' sv


c = complex kleinBottle
ht = homology Truncated $ c
hr = homology Regular c
Just ht0 = getHomology (attest :: Any N0) ht
Just hr0 = getHomology (attest :: Any N0) hr
v s = ch (Simplex (s:|Nil)) :: Chain Z N1 Symbol

{-
hmgCycles h@(Homology _ _ _ v) = case v of
  Variance _ _ _ _ (Set g) _ -> set $ amap1 (cfsssy (hmgChainSet'' h) . fromAbSlice) g
-}
