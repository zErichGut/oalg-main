
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.ChainComplex
-- Description : definition of a chain complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'ChainComplex'.
module OAlg.Homology.ChainComplex
  ( -- * Chain Complex
    ChainComplex(..), ccplPred
  , chainComplex, chainComplex', chainComplexZ

    -- ** Mapping
  , ccplMap
  ) where

import Data.Type.Equality
import Data.List as L (zip)
import Data.Maybe

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Exponential

import OAlg.Hom.Definition
import OAlg.Hom.Distributive ()

import OAlg.Entity.Natural
import OAlg.Entity.FinList as F hiding (zip) 
import OAlg.Entity.Sequence
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Simplex
import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- ChainComplex -

newtype ChainComplex t n a = ChainComplex (Diagram (Chain t) (n+3) (n+2) a) deriving (Show,Eq)

--------------------------------------------------------------------------------
-- ccplMap -

ccplMap :: Hom Dst h => h a b -> ChainComplex t n a -> ChainComplex t n b
ccplMap h (ChainComplex c) = ChainComplex (dgMap h c)

--------------------------------------------------------------------------------
-- ccplPred -

ccplPred :: Oriented a => ChainComplex t (n+1) a -> ChainComplex t n a
ccplPred (ChainComplex c) = ChainComplex $ case c of
  DiagramChainTo _ (d:|ds)   -> DiagramChainTo (start d) ds
  DiagramChainFrom _ (d:|ds) -> DiagramChainFrom (end d) ds

--------------------------------------------------------------------------------
-- ChainComplex - Entity -

instance Distributive a => Validable (ChainComplex t n a) where
  valid (ChainComplex ds) = valid ds && vldZeros ds where
    
    vldZeros :: Distributive a => Diagram (Chain t) (n+3) (n+2) a -> Statement
    vldZeros d@(DiagramChainTo _ _) = vldZerosTo 0 d
    vldZeros d@(DiagramChainFrom _ _) = vldZerosTo 0 (coDiagram d)

    vldZerosTo :: Distributive a => N -> Diagram (Chain To) (n+3) (n+2) a -> Statement
    vldZerosTo i (DiagramChainTo _ (f:|g:|Nil)) = vldZeroTo i f g 
    vldZerosTo i (DiagramChainTo _ (f:|g:|h:|ds))
      = vldZeroTo i f g && vldZerosTo (succ i) (DiagramChainTo (end g) (g:|h:|ds))

    vldZeroTo :: Distributive a => N -> a -> a -> Statement
    vldZeroTo i f g = Label (show i) :<=>: (isZero (f*g))
          :?> Params ["i":=show i,"f":=show f,"g":=show g]

--------------------------------------------------------------------------------
-- chainComplexZ -

chainComplexZ :: Ord v => Complex n v -> ChainComplex From n (Matrix Z)
chainComplexZ c = case chain c of
  DiagramChainFrom n ds -> ChainComplex (DiagramChainFrom dZero (zero (dZero :> n) :| ds))
  where

    dZero = one ()

    chain :: Ord v => Complex n v -> Diagram (Chain From) (n+2) (n+1) (Matrix Z)
    chain (Vertices vs) = DiagramChainFrom n (zero (n :> dZero):|Nil) where n = dim () ^ lengthN vs
    chain (Complex ss c) = case chain c of
      DiagramChainFrom n ds -> DiagramChainFrom m (d:|ds) where
        m = dim () ^ lengthN ss
        d = Matrix n m (rcets $ rc (listN ss) (cplIndex c))

        rc :: (N ~ i, N ~ j)
          => [(Simplex (n+1) v,j)] -> (Simplex n v -> Maybe i) -> Row j (Col i Z)
        rc ss f = Row $ PSequence $ amap1 (colj f) ss

        colj :: Ord i => (Simplex n v -> Maybe i) -> (Simplex (n+1) v,j) -> (Col i Z,j)
        colj f (s,j) = (col f (faces' s),j)

        col :: Ord i => (Simplex n v -> Maybe i) -> [Face (n+1) v] -> Col i Z
        col mf fs = colFilter (not.isZero) $ Col $ psequence (+) (alt `zip` amap1 (f mf) fs) where
          f :: (Simplex n v -> Maybe i) -> Face (n+1) v -> i
          f m (Face s) = case m s of
            Just i -> i
            _      -> error "inconsistent complex"
  
    alt :: [Z]
    alt = alt' 1 where alt' i = i:alt' (negate i)


--------------------------------------------------------------------------------
-- chainComplex -

chainComplex' :: (Hom Dst h, Ord v) => h (Matrix Z) a -> Complex n v -> ChainComplex From n a
chainComplex' h c = ccplMap h (chainComplexZ c)

chainComplex :: Ord v => Complex n v -> ChainComplex From n AbHom
chainComplex = chainComplex' FreeAbHom
