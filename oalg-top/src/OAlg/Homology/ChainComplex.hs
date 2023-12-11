
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
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Simplical
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

chainComplexZ :: Simplical s x => Complex s n x -> ChainComplex From n (Matrix Z)
chainComplexZ c = case chain c of
  (_,DiagramChainFrom n ds) -> ChainComplex (DiagramChainFrom dZero (zero (dZero :> n) :| ds))
  where

    dZero = one ()

    chain :: Simplical s x
      => Complex s n x -> (Ats n, Diagram (Chain From) (n+2) (n+1) (Matrix Z))
    chain (Vertices s) = (Ats,DiagramChainFrom n (zero (n :> dZero):|Nil)) where n = dim () ^ lengthN s
    chain c@(Complex _ c') = case chain c' of
      (Ats,DiagramChainFrom _ ds) -> (Ats,DiagramChainFrom m (d:|ds)) where
        m = start d
        d = repMatrix $ cplHomBoundary c 
  
--------------------------------------------------------------------------------
-- chainComplex -

chainComplex' :: (Hom Dst h, Simplical s x) => h (Matrix Z) a -> Complex s n x -> ChainComplex From n a
chainComplex' h c = ccplMap h (chainComplexZ c)

chainComplex :: Simplical s x => Complex s n x -> ChainComplex From n AbHom
chainComplex = chainComplex' FreeAbHom

