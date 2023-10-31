
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.Simplex
-- Description : definition of a simplex
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Simplex'.
module OAlg.Entity.Simplex
  (
    Simplex(..), Face(..)
  , faces
  ) where

import Control.Monad (join)

import Data.Type.Equality
import Data.Typeable
import Data.List (zip)
import Data.Foldable (toList)

import qualified Data.Map as M

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Exponential

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.Hom.Definition

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 
import OAlg.Entity.Sequence
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix
import OAlg.Entity.AbelianGroup.Definition
import OAlg.Entity.AbelianGroup.KernelsAndCokernels


--------------------------------------------------------------------------------
-- Simplex - 

-- | @__n__@-dimensional simplex given by @n t'+' 1@ vertices in @__v__@.
newtype Simplex n v = Simplex (FinList (n+1) v) deriving (Show,Eq,Ord)


instance Validable v => Validable (Simplex n v) where
  valid (Simplex vs) = valid vs

instance (Entity v, Typeable n) => Entity (Simplex n v)

--------------------------------------------------------------------------------
-- Face -

-- | face of a @__n__@-dimensional 'Simplex' with vertices in @__v__@.
data Face n v where
  EmptyFace :: Face N0 v
  Face      :: Simplex n v -> Face (n+1) v

deriving instance Show v => Show (Face n v)
deriving instance Eq x => Eq (Face n x)

--------------------------------------------------------------------------------
-- faceSimplex -

faceSimplex :: Face (n+1) v -> Simplex n v
faceSimplex (Face s) = s

--------------------------------------------------------------------------------
-- vertex -

vertex :: v -> Simplex N0 v
vertex v = Simplex (v:|Nil)

--------------------------------------------------------------------------------
-- (<:) -

(<:) :: v -> Face n v -> Face (n + 1) v
v <: EmptyFace           = Face (Simplex (v:|Nil))
v <: (Face (Simplex vs)) = Face (Simplex (v:|vs))

--------------------------------------------------------------------------------
-- faces -

-- | the faces of a simplex.
faces :: Simplex n v -> FinList (n + 1) (Face n v)
faces (Simplex (_:|Nil))       = EmptyFace :| Nil
faces (Simplex (v:|vs@(_:|_))) = Face (Simplex vs) :| amap1 (v<:) (faces (Simplex vs))


faces' :: Simplex n v -> [Face n v]
faces' = toList . faces

--------------------------------------------------------------------------------
-- isFace -

isFace :: Face n v -> Simplex n v -> Bool
isFace = error "nyi"

--------------------------------------------------------------------------------
-- Complex -

data Complex n v where
  Vertices :: Set v -> Complex N0 v
  -- Complex  :: Typeable n => Set (Simplex (n + 1) v) -> Complex n v -> Complex (n + 1) v
  Complex  :: Set (Simplex (n + 1) v) -> Complex n v -> Complex (n + 1) v

deriving instance Show v => Show (Complex n v)
deriving instance Eq v => Eq (Complex n v)

--------------------------------------------------------------
-- ltSimplices -

ltSimplices :: Ord v => Complex n v -> M.Map (Simplex n v) N
ltSimplices (Vertices (Set vs)) = setIndex $ Set $ amap1 vertex vs
ltSimplices (Complex s _)       = setIndex s


setIndex :: Ord x => Set x -> M.Map x N
setIndex (Set xs) = M.fromAscList (xs `zip` [0..])

instance (Validable v, Ord v, Show v) => Validable (Complex n v) where
  valid (Vertices s)           = valid s
  valid (Complex s@(Set ss) c) = valid s && valid c && vldSimplices 0 ss (ltSimplices c) where

    vldSimplices :: (Validable v, Ord v, Show v)
      => N -> [Simplex (n + 1) v] -> M.Map (Simplex n v) N -> Statement
    vldSimplices _ [] _      = SValid
    vldSimplices i (s:ss) fs = vldFaces i 0 (faces s) fs && vldSimplices (succ i) ss fs

    vldFaces :: (Validable v, Ord v, Show v)
      => N -> N -> FinList m (Face (n + 1) v) -> M.Map (Simplex n v) N -> Statement
    vldFaces _ _ Nil _ = SValid
    vldFaces i j (Face s:|ss) fs = case M.lookup s fs of
      Just _  -> vldFaces i (succ j) ss fs
      Nothing -> False :?> Params ["index (simplex,face)":=show (i,j), "simplex":=show s]

instance (Entity v, Ord v, Typeable n) => Entity (Complex n v)

--------------------------------------------------------------------------------
-- complex -

-- | generates a complex by the given simplices.
complex :: (Ord v, Attestable n) => [Simplex n v] -> Complex n v
complex = cmplx attest where
  cmplx :: Ord v => Any n -> [Simplex n v] -> Complex n v
  cmplx W0 ss = Vertices $ set $ toList $ amap1 (\(Simplex (v:|_)) -> v)  ss
  cmplx (SW n) ss = Complex (set ss) (cmplx n (amap1 faceSimplex $ join $ amap1 (faces') ss))


--------------------------------------------------------------------------------
-- triangle -

triangle :: Ord v => v -> v -> v -> Complex N2 v
triangle a b c = complex [Simplex (a:|b:|c:|Nil)]

--------------------------------------------------------------------------------
-- segment -

segment :: Ord v => v -> v -> Complex N1 v
segment a b = complex [Simplex (a:|b:|Nil)]


--------------------------------------------------------------------------------
-- ChainComplex -

newtype ChainComplex n a = ChainComplex (Diagram (Chain To) (n+3) (n+2) a) deriving (Show,Eq)

instance Distributive a => Validable (ChainComplex n a) where
  valid c@(ChainComplex ds) = valid ds && vldZeros 0 c where
    
    vldZeros :: Distributive a => N -> ChainComplex n a -> Statement
    vldZeros i c@(ChainComplex (DiagramChainTo _ (_:|_:|Nil))) = vldZero i c
    vldZeros i c@(ChainComplex (DiagramChainTo _ (_:|_:|_:|_)))
      = vldZero i c && vldZeros (succ i) (chainComplexTail c)

    vldZero :: Distributive a => N -> ChainComplex n a -> Statement
    vldZero i (ChainComplex (DiagramChainTo _ (f:|g:|_)))
      = Label (show i) :<=>: (isZero (f*g))
          :?> Params ["i":=show i,"f":=show f,"g":=show g]

--------------------------------------------------------------------------------
-- chainComplexTail -

chainComplexTail :: Distributive a => ChainComplex (n+1) a -> ChainComplex n a
chainComplexTail (ChainComplex (DiagramChainTo _ (_:|fs@(f:|_))))
  = ChainComplex (DiagramChainTo (end f) fs)

--------------------------------------------------------------------------------
-- homologies -

homology :: Distributive a => Kernels N1 a -> Cokernels N1 a -> ChainComplex n a -> Point a
homology ker coker (ChainComplex (DiagramChainTo _ (f:|g:|_))) = tip $ universalCone hCoker where

  -- image of g
  gCoker = limes coker (cokernelDiagram g)
  gIm    = limes ker (kernelDiagram $ cokernelFactor $ universalCone gCoker)

  -- kernel of f
  fKer   = limes ker (kernelDiagram f)


  h      = universalFactor fKer (ConeKernel (diagram fKer) (kernelFactor $ universalCone gIm))
  hCoker = limes coker (cokernelDiagram h)

homologies' :: Distributive a
  => Kernels N1 a -> Cokernels N1 a -> ChainComplex n a -> FinList (n+1) (Point a)
homologies' ker coker c@(ChainComplex (DiagramChainTo _ (_:|_:|Nil)))
  = homology ker coker c:|Nil
homologies' ker coker c@(ChainComplex (DiagramChainTo _ (_:|_:|_:|_)))
  = homology ker coker c:|homologies' ker coker (chainComplexTail c)

homologies :: ChainComplex n AbHom -> FinList (n+1) AbGroup
homologies = homologies' abhKernels abhCokernels

--------------------------------------------------------------------------------
-- ccMap -

ccMap :: Hom Dst h => h a b -> ChainComplex n a -> ChainComplex n b
ccMap h (ChainComplex c) = ChainComplex (dgMap h c)

--------------------------------------------------------------------------------
-- chainComplex -

chainComplexZ :: Complex n v -> ChainComplex n (Matrix Z)
chainComplexZ c = ChainComplex (chain c) where

  dZero :: Dim' Z
  dZero = one ()
  
  chain :: Complex n v -> Diagram (Chain To) (n+3) (n+2) (Matrix Z)
  chain = error "nyi"
{-  
  chain (Vertices vs) = DiagramChainTo dZero (zero (dvs :> dZero) :| zero (dZero :> dvs) :| Nil) where
    dvs = dim () ^ lengthN vs

  chain (Complex ss c) = error "nyi" 
-}
chainComplex' :: Hom Dst h => h (Matrix Z) a -> Complex n v -> ChainComplex n a
chainComplex' h c = ccMap h (chainComplexZ c)

chainComplex :: Complex n v -> ChainComplex n AbHom
chainComplex = chainComplex' FreeAbHom


--------------------------------------------------------------------------------
-- reverse -

reverse :: Attestable n => FinList n a -> FinList n a
reverse xs = let n = attest in rev n (prp1 n) xs Nil where
  rev :: Any n -> n :~: (s + t) -> FinList s a -> FinList t a -> FinList n a
  rev _ Refl Nil xs' = xs'
  rev n r@Refl (x:|xs) xs' = rev n (prp2 n r) xs (x:|xs')


  prp1 :: Any n -> n :~: (n + N0)
  prp1 = sym . prpAddNtrlR

  prp2 :: Any n -> (s + 1) :~: t -> s :~: (t + 1)
  prp2 = error "nyi"
{-  
  rev Nil ys = ys
  rev (x:|xs) ys = rev xs (x:|ys)
-}

