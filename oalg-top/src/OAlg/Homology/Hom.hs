
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Hom
-- Description : homology homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Various homology homomorphisms.
module OAlg.Homology.Hom
  (
    -- * Homology
    HomHomology, HomHomologyAtom(..)
  , homHomology, abhHomHomology
  , homChainComplex, homScpxCards
  , homCcpRepMatrix, homCcpMap
  , homDeviations, homCcpCards

    -- * Homology Trafo
  , HomHomologyTrafo, HomHomologyTrafoAtom(..)
  , HomChainComplexTrafoAtom(..)
  , HomDeviationTrafosAtom(..)
  , homHomologyTrafo, abhHomHomologyTrafo
  , homChainComplexTrafo
  , homCcptRepMatrix
  , homCcptMap
  , homDeviationTrafos
  , homCcptCards
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.Path
import OAlg.Category.Map

import OAlg.Data.Canonical

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Multiplicative
import OAlg.Structure.Distributive
import OAlg.Structure.Vectorial
import OAlg.Structure.Algebraic

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Natural as N hiding ((++))
import OAlg.Entity.Sequence.Set

import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.ConsZero

import OAlg.Hom.Definition
import OAlg.Hom.Oriented
import OAlg.Hom.Multiplicative
import OAlg.Hom.Fibred
import OAlg.Hom.Additive
import OAlg.Hom.Distributive
import OAlg.Hom.Vectorial
import OAlg.Hom.Algebraic

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator
import OAlg.Homology.ChainComplex
import OAlg.Homology.SomeComplex.Definition

--------------------------------------------------------------------------------
-- HomHomologyAtom -

data HomHomologyAtom s r n a b where
  ChainComplex :: SimplexType s -> Regular -> Any n
    -> HomHomologyAtom s r n SomeComplex (ChainComplex n (ChainOperator r s))
  ScpxCards :: Any n ->  HomHomologyAtom s r n SomeComplex (Cards r n)
  CcpRepMatrix
    :: HomHomologyAtom s r n (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
  CcpMap :: Hom Dst h => h (Matrix r) a
    -> HomHomologyAtom s r n (ChainComplex n (Matrix r)) (ChainComplex n a)
  Deviations :: Distributive a => Kernels N1 a -> Cokernels N1 a
    -> HomHomologyAtom s r n (ChainComplex n a) (Deviation (n+1) a)
  CcpCards :: HomHomologyAtom s r n (ChainComplex n (ChainOperator r s)) (Cards r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => Morphism (HomHomologyAtom s r n) where
  type ObjectClass (HomHomologyAtom s r n) = Ent
  homomorphous (ChainComplex _ _ _) = Struct :>: Struct
  homomorphous (ScpxCards _)        = Struct :>: Struct
  homomorphous CcpRepMatrix         = Struct :>: Struct
  homomorphous (CcpMap h)           = case  dstRng h of Struct -> Struct :>: Struct
    where dstRng :: Hom Dst h => h a b -> Struct Dst b
          dstRng = tau . range
  homomorphous (Deviations _ _)     = Struct :>: Struct
  homomorphous CcpCards             = Struct :>: Struct

instance (AlgebraicRing r, Ord r, Typeable s)
  => Applicative (HomHomologyAtom s r n) where
  amap (ChainComplex s r n)     = \(SomeComplex c) -> chainComplex (structSmpl s c) r n c
  amap (ScpxCards n)            = scpxCards n
  amap CcpRepMatrix             = ccpRepMatrix
  amap (CcpMap h)               = case range h of Struct -> cnzMap h
  amap (Deviations kers cokers) = deviations kers cokers 
  amap CcpCards                 = ccpCards


--------------------------------------------------------------------------------
-- HomHomology -

type HomHomology s r n = Path (HomHomologyAtom s r n)

--------------------------------------------------------------------------------
-- homChainComplex -

homChainComplex :: SimplexType s -> Regular -> Any n
  -> HomHomology s r n SomeComplex (ChainComplex n (ChainOperator r s))
homChainComplex s r n = ChainComplex s r n :. IdPath Struct

--------------------------------------------------------------------------------
-- homScpxCards -

homScpxCards :: Any n -> HomHomology s r n SomeComplex (Cards r n)
homScpxCards n = ScpxCards n :. IdPath Struct

homScpxCards' :: Any n ->  HomHomology Set Z n SomeComplex (Cards Z n)
homScpxCards' = homScpxCards

--------------------------------------------------------------------------------
-- homCcpRepMatrix -

homCcpRepMatrix :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomHomology s r n (ChainComplex n (ChainOperator r s)) (ChainComplex n (Matrix r))
homCcpRepMatrix = CcpRepMatrix :. IdPath Struct

--------------------------------------------------------------------------------
-- homCcpMap -

homCcpMap :: (AlgebraicRing r, Typeable n, Hom Dst h)
  => h (Matrix r) a
  -> HomHomology s r n (ChainComplex n (Matrix r)) (ChainComplex n a)
homCcpMap h = CcpMap h :. IdPath Struct

--------------------------------------------------------------------------------
-- homDeviations -

homDeviations :: (Distributive a, Typeable n)
  => Kernels N1 a -> Cokernels N1 a
  -> HomHomology s r n (ChainComplex n a) (Deviation (n+1) a)
homDeviations kers cokers = Deviations kers cokers :. IdPath Struct

--------------------------------------------------------------------------------
-- homCcpCards -

homCcpCards :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomHomology s r n (ChainComplex n (ChainOperator r s)) (Cards r n)
homCcpCards = CcpCards :. IdPath Struct

--------------------------------------------------------------------------------
-- homHomology -

homHomology :: ( AlgebraicRing r, Ord r, Typeable s, Typeable n
               , Hom Dst h, Distributive a
               )
  => SimplexType s -> Regular -> Any n
  -> h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> HomHomology s r n SomeComplex (Deviation (n+1) a)
homHomology s r n h kers cokers
  = homDeviations kers cokers . homCcpMap h . homCcpRepMatrix . homChainComplex s r n

--------------------------------------------------------------------------------
-- abhHomHomology -

abhHomHomology :: (Typeable s, Typeable n)
  => SimplexType s -> Regular -> Any n
  -> HomHomology s Z n SomeComplex (Deviation (n+1) AbHom)
abhHomHomology s r n = homHomology s r n FreeAbHom kers cokers where
  kers   = abhKernels
  cokers = abhCokernels
  
--------------------------------------------------------------------------------
-- HomChainComplexTrafoAtom -

data HomChainComplexTrafoAtom s r n a b where
  ChainComplexTrafo :: HomologyType s -> Regular -> Any n
    -> HomChainComplexTrafoAtom s r n (SomeComplexMap s) (ChainComplexTrafo n (ChainOperator r s))

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => Morphism (HomChainComplexTrafoAtom s r n) where
  type ObjectClass (HomChainComplexTrafoAtom s r n) = Mlt
  homomorphous (ChainComplexTrafo _ _ _) = Struct :>: Struct

instance (AlgebraicRing r, Ord r)
  => Applicative (HomChainComplexTrafoAtom s r n) where
  amap (ChainComplexTrafo s r n) (SomeComplexMap f) = case entOrdComplexMap f of
    (Struct,Struct) -> chainComplexTrafo (structHmlg s f) r n f

ccth :: HomChainComplexTrafoAtom s r n a b -> HomHomologyAtom s r n (Point a) (Point b)
ccth (ChainComplexTrafo s r n) = ChainComplex (inj s) r n

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomOriented (HomChainComplexTrafoAtom s r n) where
  pmap = amap . ccth

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomMultiplicative (HomChainComplexTrafoAtom s r n)

--------------------------------------------------------------------------------
-- HomDeviationTrafosAtom -

data HomDeviationTrafosAtom s r n a b where
  CcptRepMatrix
    :: HomDeviationTrafosAtom s r n
         (ChainComplexTrafo n (ChainOperator r s))
         (ChainComplexTrafo n (Matrix r))
  CcptMap
    :: Hom (Alg r) h => h (Matrix r) a
    -> HomDeviationTrafosAtom s r n (ChainComplexTrafo n (Matrix r)) (ChainComplexTrafo n a)
  DeviationTrafos
    :: (Algebraic a, Scalar a ~ r)
    => Kernels N1 a -> Cokernels N1 a
    -> HomDeviationTrafosAtom s r n (ChainComplexTrafo n a) (DeviationTrafo (n+1) a)
  CcptCards
    :: HomDeviationTrafosAtom s r n (ChainComplexTrafo n (ChainOperator r s)) (CardsTrafo r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => Morphism (HomDeviationTrafosAtom s r n) where
  type ObjectClass (HomDeviationTrafosAtom s r n) = Alg r
  homomorphous CcptRepMatrix         = Struct :>: Struct
  homomorphous (CcptMap h)           = case algRng h of Struct -> Struct :>: Struct
    where algRng :: Hom (Alg r) h => h (Matrix r) b -> Struct (Alg r) b
          algRng = tau . range
  homomorphous (DeviationTrafos _ _) = Struct :>: Struct          
  homomorphous CcptCards             = Struct :>: Struct
  
instance (AlgebraicRing r, Ord r, Typeable s)
  => Applicative (HomDeviationTrafosAtom s r n) where
  amap CcptRepMatrix                 = ccptRepMatrix
  amap (CcptMap h)                   = case range h of Struct -> cnztMap h
  amap (DeviationTrafos kers cokers) = deviationTrafos kers cokers
  amap CcptCards                     = ccptCards

dth :: HomDeviationTrafosAtom s r n a b -> HomHomologyAtom s r n (Point a) (Point b)
dth CcptRepMatrix = CcpRepMatrix
dth (CcptMap h)   = CcpMap h
dth (DeviationTrafos kers cokers) = Deviations kers cokers
dth CcptCards     = CcpCards

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomOriented (HomDeviationTrafosAtom s r n) where
  pmap = amap . dth

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomMultiplicative (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomFibred (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomAdditive (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomVectorial r (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomFibredOriented (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomDistributive (HomDeviationTrafosAtom s r n)

instance (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomAlgebraic r (HomDeviationTrafosAtom s r n)

--------------------------------------------------------------------------------
-- HomHomologyTrafoAtom -

data HomHomologyTrafoAtom s r n a b where
  HomChainComplexTrafoAtom
    :: HomChainComplexTrafoAtom s r n a b -> HomHomologyTrafoAtom s r n a b
  HomDeviationTrafosAtom
    :: HomDeviationTrafosAtom s r n a b -> HomHomologyTrafoAtom s r n a b

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => Morphism (HomHomologyTrafoAtom s r n) where
  type ObjectClass (HomHomologyTrafoAtom s r n) = Mlt
  homomorphous (HomChainComplexTrafoAtom o) = homomorphous o
  homomorphous (HomDeviationTrafosAtom o)   = homomorphous (Forget o)

instance (AlgebraicRing r, Ord r, Typeable s)
  => Applicative (HomHomologyTrafoAtom s r n) where
  amap (HomChainComplexTrafoAtom h) = amap h
  amap (HomDeviationTrafosAtom h)   = amap h

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomOriented (HomHomologyTrafoAtom s r n) where
  pmap (HomChainComplexTrafoAtom h) = pmap h
  pmap (HomDeviationTrafosAtom h)   = pmap h

instance (AlgebraicRing r, Ord r, MultiplicativeComplexMap s, Typeable n)
  => HomMultiplicative (HomHomologyTrafoAtom s r n) 

--------------------------------------------------------------------------------
-- HomHomologyTrafo -

type HomHomologyTrafo s r n = Path (HomHomologyTrafoAtom s r n)

--------------------------------------------------------------------------------
-- homChainComplexTrafo -

homChainComplexTrafo :: MultiplicativeComplexMap s
  => HomologyType s -> Regular -> Any n
  -> HomHomologyTrafo s r n (SomeComplexMap s) (ChainComplexTrafo n (ChainOperator r s))
homChainComplexTrafo s r n = (HomChainComplexTrafoAtom $ ChainComplexTrafo s r n) :. IdPath Struct

--------------------------------------------------------------------------------
-- homCcptRepMatrix -

homCcptRepMatrix :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomHomologyTrafo s r n (ChainComplexTrafo n (ChainOperator r s)) (ChainComplexTrafo n (Matrix r))
homCcptRepMatrix = (HomDeviationTrafosAtom CcptRepMatrix) :. IdPath Struct

--------------------------------------------------------------------------------
-- homCcptMap -

homCcptMap :: (Hom (Alg r) h, AlgebraicRing r, Typeable n)
  => h (Matrix r) a
  -> HomHomologyTrafo s r n (ChainComplexTrafo n (Matrix r)) (ChainComplexTrafo n a)
homCcptMap h = (HomDeviationTrafosAtom $ CcptMap h) :. IdPath Struct

--------------------------------------------------------------------------------
-- homDeviationTrafos -

homDeviationTrafos :: (Algebraic a, Scalar a ~ r, Typeable n)
  => Kernels N1 a -> Cokernels N1 a
  -> HomHomologyTrafo s r n (ChainComplexTrafo n a) (DeviationTrafo (n+1) a)
homDeviationTrafos kers cokers
  = (HomDeviationTrafosAtom $ DeviationTrafos kers cokers) :. IdPath Struct

--------------------------------------------------------------------------------
-- homCcptCards -

homCcptCards :: (AlgebraicRing r, Ord r, Typeable s, Typeable n)
  => HomHomologyTrafo s r n (ChainComplexTrafo n (ChainOperator r s)) (CardsTrafo r n)
homCcptCards = (HomDeviationTrafosAtom CcptCards) :. IdPath Struct

--------------------------------------------------------------------------------
-- homHomologyTrafo -

homHomologyTrafo
  :: ( AlgebraicRing r, Ord r
     , MultiplicativeComplexMap s, Typeable n
     , Hom (Alg r) h
     , Algebraic a, Scalar a ~ r
     )
  => HomologyType s -> Regular -> Any n
  -> h (Matrix r) a -> Kernels N1 a -> Cokernels N1 a
  -> HomHomologyTrafo s r n (SomeComplexMap s) (DeviationTrafo (n+1) a)
homHomologyTrafo s r n h kers cokers
  = homDeviationTrafos kers cokers
  . homCcptMap h
  . homCcptRepMatrix
  . homChainComplexTrafo s r n

--------------------------------------------------------------------------------
-- abhHomHomologyTrafo -

abhHomHomologyTrafo :: (MultiplicativeComplexMap s, Typeable n)
  => HomologyType s -> Regular -> Any n
  -> HomHomologyTrafo s Z n (SomeComplexMap s) (DeviationTrafo (n+1) AbHom)
abhHomHomologyTrafo s r n = homHomologyTrafo s r n FreeAbHom kers cokers where
  kers   = abhKernels
  cokers = abhCokernels
  
--------------------------------------------------------------------------------

s = complex [Set "ab",Set "bc",Set "ac"]
t = cpxProductAsc s s

p1 = ComplexMapNgl t s (Map fst)
p2 = ComplexMapNgl t s (Map snd)

crds :: (MultiplicativeComplexMap s, Typeable n)
  => HomologyType s -> Regular -> Any n
  -> HomHomologyTrafo s Z n (SomeComplexMap s) (CardsTrafo Z n)
crds s r n = homCcptCards . homChainComplexTrafo s r n
