
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : definition of homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- definition of 'Homology'.
module OAlg.Homology.Definition
  (
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Map

import OAlg.Data.Canonical
import OAlg.Data.Either

import OAlg.Structure.Additive
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Algebraic

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Diagram

import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.ConsZero

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex
import OAlg.Homology.SomeComplex.Definition

--------------------------------------------------------------------------------
-- Homology -

type Homology n = Deviation (n+1)

--------------------------------------------------------------------------------
-- HomologyOperatorAtom -

data HomologyOperatorAtom n r s a b where
  ChainComplex :: SimplexType s -> Regular -> Any n
    -> HomologyOperatorAtom n r s SomeComplex (ChainComplex n (ChainOperator r s))
  ScpxCards :: Any n ->  HomologyOperatorAtom n r s SomeComplex (Cards (n+3))
  CcpRepMatrix
    :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
  CcpMap :: Hom Dst h => h (Matrix r) a
    -> HomologyOperatorAtom n r s (ChainComplex n (Matrix r)) (ChainComplex n a)
  Deviations :: Distributive a => Kernels N1 a -> Cokernels N1 a
    -> HomologyOperatorAtom n r s (ChainComplex n a) (Homology n a)
  CcpCards :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (Cards (n+3))

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => Morphism (HomologyOperatorAtom n r s) where
  type ObjectClass (HomologyOperatorAtom n r s) = Ent
  homomorphous (ChainComplex _ _ _) = Struct :>: Struct
  homomorphous (ScpxCards _)        = Struct :>: Struct
  homomorphous CcpRepMatrix         = Struct :>: Struct
  homomorphous (CcpMap h)           = case  dstRng h of Struct -> Struct :>: Struct
    where dstRng :: Hom Dst h => h a b -> Struct Dst b
          dstRng = tau . range
  homomorphous (Deviations _ _)     = Struct :>: Struct
  homomorphous CcpCards             = Struct :>: Struct

instance (AlgebraicRing r, Ord r, Typeable s)
  => Applicative (HomologyOperatorAtom n r s) where
  amap (ChainComplex s r n)     = \(SomeComplex c) -> chainComplex (structSmpl s c) r n c
  amap (ScpxCards n)            = scpxCards n
  amap CcpRepMatrix             = ccpRepMatrix
  amap (CcpMap h)               = case range h of Struct -> cnzMap h
  amap (Deviations kers cokers) = deviations kers cokers 
  amap CcpCards                 = ccpCards

--------------------------------------------------------------------------------
-- HomologyOperator -

type HomologyOperator n r s = Path (HomologyOperatorAtom n r s)

--------------------------------------------------------------------------------
-- chainComplexOpr -

chainComplexOpr :: SimplexType s -> Regular -> Any n
  -> HomologyOperator n r s SomeComplex (ChainComplex n (ChainOperator r s))
chainComplexOpr s r n = ChainComplex s r n :. IdPath Struct

--------------------------------------------------------------------------------
-- scpxCardsOpr -

scpxCardsOpr :: Any n -> HomologyOperator n r s SomeComplex (Cards (n+3))
scpxCardsOpr n = ScpxCards n :. IdPath Struct

scpxCardsOpr' :: Any n ->  HomologyOperator n Z Set SomeComplex (Cards (n+3))
scpxCardsOpr' = scpxCardsOpr

--------------------------------------------------------------------------------
-- ccpRepMatrixOpr -

ccpRepMatrixOpr :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomologyOperator n r s (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
ccpRepMatrixOpr = CcpRepMatrix :. IdPath Struct

--------------------------------------------------------------------------------
-- ccpMapOpr -

ccpMapOpr :: (AlgebraicRing r, Typeable n, Hom Dst h)
  => h (Matrix r) a
  -> HomologyOperator n r s (ChainComplex n (Matrix r)) (ChainComplex n a)
ccpMapOpr h = CcpMap h :. IdPath Struct

--------------------------------------------------------------------------------
-- deviationsOpr -

deviationsOpr :: (Distributive a, Typeable n)
  => Kernels N1 a -> Cokernels N1 a
  -> HomologyOperator n r s (ChainComplex n a) (Homology n a)
deviationsOpr kers cokers = Deviations kers cokers :. IdPath Struct

--------------------------------------------------------------------------------
-- ccpCardsOpr -

ccpCardsOpr :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomologyOperator n r s (ChainComplex n (ChainOperator r s)) (Cards (n+3))
ccpCardsOpr = CcpCards :. IdPath Struct

--------------------------------------------------------------------------------
-- homologyOpr -

homologyOpr :: ( AlgebraicRing r, Ord r, Typeable s, Typeable n
               , Hom Dst h, Distributive a
               )
  => SimplexType s -> Regular -> Any n
  -> h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> HomologyOperator n r s SomeComplex (Homology n a)
homologyOpr s r n h kers cokers
  = deviationsOpr kers cokers . ccpMapOpr h . ccpRepMatrixOpr . chainComplexOpr s r n

--------------------------------------------------------------------------------
-- homology -

-- | the clasical homology 
homology :: Typeable n => Any n -> SomeComplex -> Homology n AbHom
homology n  = amap (homologyOpr SpxTypeSet Regular n h kers cokers) where
  h      = FreeAbHom
  kers   = abhKernels
  cokers = abhCokernels

--------------------------------------------------------------------------------

s = complex [Set "ab", Set "bc",Set "ac"]
t = cpxProductAsc s s

--------------------------------------------------------------------------------
-- ChainComplexTrafoOperatorAtom -

data ChainComplexTrafoOperatorAtom n r s a b where
  ChainComplexTrafo :: HomologyType s -> Regular -> Any n
    -> ChainComplexTrafoOperatorAtom n r s (SomeComplexMap s) (ChainComplexTrafo n (ChainOperator r s))
{-    
  CcptCards :: ChainComplexTrafoOperatorAtom n r s
                 (ChainComplexTrafo n (ChainOperator r s))
                 (CardsTrafo (n+3))
-}

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => Morphism (ChainComplexTrafoOperatorAtom n r s) where
  type ObjectClass (ChainComplexTrafoOperatorAtom n r s) = Mlt
  homomorphous (ChainComplexTrafo _ _ _) = Struct :>: Struct

instance (AlgebraicRing r, Ord r)
  => Applicative (ChainComplexTrafoOperatorAtom n r s) where
  amap (ChainComplexTrafo s r n) (SomeComplexMap f) = case entOrdComplexMap f of
    (Struct,Struct) -> chainComplexTrafo (structHmlg s f) r n f

cctoho :: ChainComplexTrafoOperatorAtom n r s a b -> HomologyOperatorAtom n r s (Point a) (Point b)
cctoho (ChainComplexTrafo s r n) = ChainComplex (inj s) r n

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomOriented (ChainComplexTrafoOperatorAtom n r s) where
  pmap t = amap $ cctoho t

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomMultiplicative (ChainComplexTrafoOperatorAtom n r s)



{-
--------------------------------------------------------------------------------
-- HomologyOperatorAtom -

data HomologyOperatorAtom n r s x y where
  R :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
  M :: Hom Dst h => h (Matrix r) a
    -> HomologyOperatorAtom n r s (ChainComplex n (Matrix r)) (ChainComplex n a)
  H :: Distributive a => Kernels N1 a -> Cokernels N1 a
    -> HomologyOperatorAtom n r s (ChainComplex n a) (Homology n a)
    
  U :: Any n ->  HomologyOperatorAtom n r s SomeComplex (Cards (n+3))
  V :: HomologyOperatorAtom n r s (ChainComplex n (ChainOperator r s)) (Cards (n+3))


instance (AlgebraicRing r, Ord r, Typeable s)
  => Applicative (HomologyOperatorAtom n r s) where
  amap (C s r n)       = \(SomeComplex c) -> chainComplex (structSmpl s c) r n c
  amap R               = ccpRepMatrix
  amap (M h)           = case range h of Struct -> cnzMap h
  amap (H kers cokers) = deviations kers cokers 
  amap (U n)           = scpxCards n
  amap V               = ccpCards

--------------------------------------------------------------------------------
-- HomologyOperator -

type HomologyOperator n r s = Path (HomologyOperatorAtom n r s)

--------------------------------------------------------------------------------
-- HomologyTrafo -

type HomologyTrafo n = DeviationTrafo (n+1)

--------------------------------------------------------------------------------
-- HomologyTrafoOperatorAtom -

data HomologyTrafoOperatorAtom n r s x y where
  CT :: HomologyType s -> Regular -> Any n
     -> HomologyTrafoOperatorAtom n r s (SomeComplexMap s) (ChainComplexTrafo n (ChainOperator r s))

--------------------------------------------------------------------------------
-- hmgOprAtom -

hmgOprAtom :: HomologyTrafoOperatorAtom n r s x y -> HomologyOperatorAtom n r s (Point x) (Point y)
hmgOprAtom (CT hmgT r n) = C (inj hmgT) r n

--------------------------------------------------------------------------------
-- HomologyTrafoOperatorAtom - Hom -

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => Morphism (HomologyTrafoOperatorAtom n r s) where
  type ObjectClass (HomologyTrafoOperatorAtom n r s) = Mlt
  homomorphous (CT _ _ _) = Struct :>: Struct

instance (AlgebraicRing r, Ord r) => Applicative (HomologyTrafoOperatorAtom n r s) where
  amap (CT s r n) = \(SomeComplexMap f) -> case entOrdComplexMap f of
                      (Struct,Struct)   -> chainComplexTrafo (structHmlg s f) r n f

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomOriented (HomologyTrafoOperatorAtom n r s) where
  pmap o = amap $ hmgOprAtom o
-}


{-
------------------------------------------------------------------------------------------
-- homologyTrafo -

homologyTrafo :: ( Hom Dst h
                 , AlgebraicSemiring r, Ring r, Ord r, Typeable s
                 , Distributive a
                 )
  => h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> ChainComplexTrafo n (ChainOperator r s) -> HomologyTrafo n a
homologyTrafo h kers cokers = deviationTrafos kers cokers . cnztMap h . ccptRepMatrix
-}
{-
hmgt :: (Homological s x y) => Regular -> Any n
  -> ComplexMap s (Complex x) (Complex y) -> HomologyTrafo n AbHom
hmgt r n f = homologyTrafo FreeAbHom abhKernels abhCokernels $ ccpt r n f where
  ccpt :: (Homological s x y)
       => Regular -> Any n -> ComplexMap s (Complex x) (Complex y)
       -> ChainComplexTrafo n (ChainOperator Z s)
  ccpt = chainComplexTrafo
-}
