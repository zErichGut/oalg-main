
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, TupleSections #-}

-- |
-- Module      : OAlg.Topology.Limes.EqualizersAndCoequalizers
-- Description : equalizers and coequalizers.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Equalizers and coequalizers.
module OAlg.Topology.Limes.EqualizersAndCoequalizers
  (
  ) where

import Control.Monad as M

-- import Data.Typeable

import Data.List (zip)

import OAlg.Prelude

import OAlg.Category.Map

-- import OAlg.Data.Either
-- import OAlg.Data.Filterable

import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Ring
-- import OAlg.Structure.PartiallyOrdered

-- import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip)
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph

import OAlg.Entity.Matrix

import OAlg.Limes.Definition
import OAlg.Limes.Cone
-- import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation

import OAlg.Homology.Simplical hiding (simplex,dimension)
import OAlg.Homology.Complex -- hiding (cpxProduct, cpxProductAsc)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition hiding (B,D,F)

import OAlg.Topology.Definition
-- import OAlg.Topology.Limes.TerminalAndInitialSpace

import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- Vertex -

data Vertex where Vertex :: (Entity x, Ord x) => x -> Vertex

--------------------------------------------------------------------------------
-- connectionClasses -

-- | the various connection classes.
connectionClasses :: Space m -> Matrix F2
connectionClasses u@(SpaceConcrete _) = connectionClasses $ spcAbstract u
connectionClasses u@(SpaceAbstract cx) = p * v where
  p = cokernelFactor $ universalCone ckr
  v = universalFactor kr (ConeKernel d o) where
    d = universalDiagram kr
    o = one $ end $ kernelFactor $ universalCone kr

  VarianceG _ ((kr,ckr):|Nil) = homology f2 cf

  cc = chainComplex ChainComplexStandard SpxTypeSet (attest :: Any N0) cx
  cf = pmap (hF f2 . hZ) cc
  f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)

--------------------------------------------------------------------------------
-- psqList -

-- | the list given by a partially defined sequence with the given length, where the omitted elements
-- are set by the given default value.
psqList :: N -> x -> PSequence N x -> [x]
psqList iL xD (PSequence xis) = psq 0 xD xis where
  psq :: N -> x -> [(x,N)] -> [x]
  psq i _ _ | iL <= i        = []
  psq i xD []                = xD : psq (i+1) xD []
  psq i xD xis@((x,i'):xis') = if i < i'
    then (xD:psq (i+1) xD xis)
    else (x:psq (i+1) xD xis')

--------------------------------------------------------------------------------
-- mtxColVecs -

-- | the columns as a list of vectors.
mtxColVecs :: Semiring x => Matrix x -> [Vector x]
mtxColVecs m = vcs (cols m) (mtxRowCol m) where
  vcs :: Semiring x => Dim' x -> Row N (Col N x) -> [Vector x]
  vcs cls (Row xjs) = psqList (lengthN cls) (zero ()) $ psqMap toVec xjs

  toVec :: Col N x -> Vector x
  toVec (Col xis) = Vector xis
   
--------------------------------------------------------------------------------
-- cpxConnectionGraph -

-- | the connection classes of a complex, represented as a 'Graph' where the first component of its
-- associations is a vertex in the given complex together with its connection class - i.e. the
-- @0@-th homology class according to 'F2' - represented by a 'Vector' over 'F2'. 
cpxConnectionGraph :: (Entity x, Ord x) => Complex x -> Graph x (Vector F2)
cpxConnectionGraph cx = Graph (vx `zip` mtxColVecs (p * v)) where
  vx = setxs $ cpxVertices cx
  
  p = cokernelFactor $ universalCone ckr
  v = universalFactor kr (ConeKernel d o) where
    d = universalDiagram kr
    o = one $ end $ kernelFactor $ universalCone kr

  VarianceG _ ((kr,ckr):|Nil) = homology f2 cf

  cc = chainComplex ChainComplexStandard SpxTypeSet (attest :: Any N0) cx
  cf = pmap (hF f2 . hZ) cc
  f2 = HmlgF :: f ~ F2 => Homological f (Matrix f)


--------------------------------------------------------------------------------
-- cpxMap -

-- | the induced complex map with domain equal to the given one.
cpxMapStruct :: Homomorphous EntOrd x y
  -> Complex x -> Map EntOrd x y -> ComplexMap [] (Complex x) (Complex y)
cpxMapStruct s@(Struct:>:Struct) a f = ComplexMap SpxTypeLst a b f where
  b = complex $ join $ amap1 (setxs . amap1 (mapSet s f) . snd) $ gphxs $ cpxGenerators a
  
  mapSet :: Homomorphous EntOrd x y -> Map EntOrd x y -> Map EntOrd (Set x) (Set y)
  mapSet (Struct:>:Struct) f = Map (amapG f) 

-- | the induced complex map with domain equal to the given one.
cpxMap :: Complex x -> Map EntOrd x y -> ComplexMap [] (Complex x) (Complex y)
cpxMap c f = cpxMapStruct (homomorphous f) c f

--------------------------------------------------------------------------------
--
s :: Complex Symbol
s = complex [Set [A,B],Set [B,C],Set [D,E],Set [F]] 

f :: Map EntOrd Symbol (Vector F2)
f = Map (fromJust . gphLookup (cpxConnectionGraph s))

ff :: ComplexMap [] (Complex Symbol) (Complex (Vector F2))
ff = cpxMap s f
