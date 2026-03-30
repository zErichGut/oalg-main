
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Entity.FactorM
-- Description : mono and epi morphic factors.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- mono- and epimorphic factors for 'Multiplicative' structures.
module OAlg.Entity.FactorM
  ( -- * FactorM
    FactorM(..), Morphology(..)

    -- * Mapping
  , fcmMapCov, fcmMapCnt, fcmMapS

    -- * Limes
  , kernelFactorMono, cokernelFactorEpi

    -- * Proposition
  , relFactorM, FactorMDiagram(..)
  , fmdMapCov, fmdMapCnt, fmdMapS
  , xoFactorMDiagram
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Data.Variant
import OAlg.Data.Either

import OAlg.Category.SDuality

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Multiplicative

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

--------------------------------------------------------------------------------
-- Morphology -

-- | morphology of a 'FactorM', i.e. either mono- or epimorph
data Morphology = Monomorph | Epimorph deriving (Show,Read,Ord,Eq,Enum,Bounded)

type instance Dual Monomorph = Epimorph
type instance Dual Epimorph  = Monomorph

instance Validable Morphology where
  valid Monomorph = SValid
  valid _         = SValid

--------------------------------------------------------------------------------
-- FactorM -

-- | mono- and epimorphic arrows within a 'Multiplicative' structure.
--
-- __Property__ Let @m@ be in @'FactorM' __m x__@ where @__x__@ is a 'Multiplicative'
-- structure, then holds:
--
-- (1) If @m@ matches @'Mono' i@ for some @i@ in @__x__@ then holds:
-- For all parrallel @f@, @g@ in @__x__@ - i.e. @'orientation' f '==' 'orientation' g@ - with
-- @'end' f '==' 'start' i@ and @i '*' f '==' i '*' g@ follows that @f '==' g@.
--
-- (2) If @m@ matches @'Epi' p@ for some @p@ in @__x__@ then holds:
-- For all parrallel @f@, @g@ in @__x__@ - i.e. @'orientation' f '==' 'orientation' g@ - with
-- @'start' f '==' 'end' p@ and @f '*' p '==' g '*' p@ follows that @f '==' g@.
data FactorM m x where
  Mono :: x -> FactorM Monomorph x
  Epi  :: x -> FactorM Epimorph x

deriving instance Show x => Show (FactorM m x)
deriving instance Eq x => Eq (FactorM m x)
deriving instance Ord x => Ord (FactorM m x)

--------------------------------------------------------------------------------
-- fcmMapCov -

-- | covariant mapping of a 'FactorM'.
--
-- __Note__ We use isomorphisms to preserve monomorphic factors.
fcmMapCov :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h)
  => Variant2 Covariant (Inv2 h) x y -> FactorM m x -> FactorM m y
fcmMapCov (Covariant2 i) (Mono x) = Mono $ amap i x
fcmMapCov (Covariant2 i) (Epi x)  = Epi $ amap i x

--------------------------------------------------------------------------------
-- fcmMapCnt -

-- | contravariant mapping of a 'FactorM'.
--
-- __Note__ We use isomorphisms for mappings between  mono- and epimorphic factors.
fcmMapCnt :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h)
  => Variant2 Contravariant (Inv2 h) x y -> FactorM m x -> FactorM (Dual m) y
fcmMapCnt (Contravariant2 i) (Mono x) = Epi $ amap i x
fcmMapCnt (Contravariant2 i) (Epi x)  = Mono $ amap i x

--------------------------------------------------------------------------------
-- fcmMapS -

type instance Dual1 (FactorM m) = FactorM (Dual m)

-- | mapping of 'FactorM'.
fcmMapS :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Inv2 h x y -> SDualBi (FactorM m) x -> SDualBi (FactorM m) y
fcmMapS = vmapBi fcmMapCov fcmMapCov fcmMapCnt fcmMapCnt

instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => ApplicativeG (SDualBi (FactorM m)) (Inv2 h) (->) where
  amapG = fcmMapS

instance (CategoryDisjunctive h, Functorial h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => FunctorialG (SDualBi (FactorM m)) (Inv2 h) (->)
  
--------------------------------------------------------------------------------
-- kernelFactorMono -

-- | the monomorphic factor of its universal shell.
kernelFactorMono :: Kernel n x -> FactorM Monomorph x
kernelFactorMono =  Mono . kernelFactor . universalCone

--------------------------------------------------------------------------------
-- cokernelFactorEpi -

-- | the epimorphic factor of its universal shell.
cokernelFactorEpi :: Cokernel n x -> FactorM Epimorph x
cokernelFactorEpi = Epi . cokernelFactor . universalCone

--------------------------------------------------------------------------------
-- FactorMDiagram -

-- | diagram for validating 'FactorM'.
--
-- __Property__ Let @d@ be in @'FactorMDiagram' __m x__@ where @__x__@ is a 'Multiplicative' structure,
-- then holds:
--
--  (1) If @d@ matches @'FactorMDiagram' ('Mono' i) (f,g)@, then holds:
--
--      (1) @'orientation' f '==' 'orientation' g@.
--
--      (2) @'end' f '==' 'start' i@.
--
--  (2) If @d@ matches @'FactorMDiagram' ('Epi' i) (f,g)@, then holds:
--
--      (1) @'orientation' f '==' 'orientation' g@.
--
--      (2) @'start' f '==' 'end' i@.
data FactorMDiagram m x = FactorMDiagram (FactorM m x) (x,x) deriving (Show,Eq,Ord)

--------------------------------------------------------------------------------
-- mapping -

-- | covariant mapping of a 'FactorMDiagram'.
fmdMapCov :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Variant2 Covariant (Inv2 h) x y -> FactorMDiagram m x -> FactorMDiagram m y
fmdMapCov (Covariant2 h) (FactorMDiagram i (f,g)) = FactorMDiagram i' (f',g') where
  SDualBi (Right1 i') = amapF h (SDualBi (Right1 i))
  f'                  = amap h f
  g'                  = amap h g

-- | contravariant mapping of a 'FactorMDiagram'.
fmdMapCnt :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Variant2 Contravariant (Inv2 h) x y -> FactorMDiagram m x -> FactorMDiagram (Dual m) y
fmdMapCnt (Contravariant2 h) (FactorMDiagram i (f,g)) = FactorMDiagram i' (f',g') where
  SDualBi (Left1 i')  = amapF h (SDualBi (Right1 i))
  f'                  = amap h f
  g'                  = amap h g

type instance Dual1 (FactorMDiagram m) = FactorMDiagram (Dual m)

-- | mapping of a 'FactorMDiagram'.
fmdMapS :: (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => Inv2 h x y -> SDualBi (FactorMDiagram m) x -> SDualBi (FactorMDiagram m) y
fmdMapS = vmapBi fmdMapCov fmdMapCov fmdMapCnt fmdMapCnt

instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => ApplicativeG (SDualBi (FactorMDiagram m)) (Inv2 h) (->) where
  amapG = fmdMapS
  
instance (CategoryDisjunctive h, Functorial h, HomMultiplicativeDisjunctive h, Dual (Dual m) ~ m)
  => FunctorialG (SDualBi (FactorMDiagram m)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- xoFactorMDiagram -

xoFactorMDiagram :: Multiplicative x => XOrtOrientation x -> FactorM m x -> X (FactorMDiagram m x)
xoFactorMDiagram xo m@(Mono i) = do
  s <- xoPoint xo
  f <- xoArrow xo (s :> end i)
  g <- xoArrow xo (s :> end i)
  return (FactorMDiagram m (f,g))
xoFactorMDiagram xo m@(Epi _)
  = amap1 (fmdMapCnt $ Contravariant2 $ inv2 i) $ xoFactorMDiagram xo' m' where
  
    xo'                = coXOrtOrientation xo
    Contravariant2 i   = toDualOpMlt
    SDualBi (Left1 m') = amapF i (SDualBi (Right1 m))
  
--------------------------------------------------------------------------------
-- relFactroMDiagram -

relFactorMDiagram :: Multiplicative x => FactorMDiagram m x -> Statement
relFactorMDiagram (FactorMDiagram (Mono i) (f,g))
  = And [ Label "1.1" :<=>: (orientation f == orientation g) :?> Params ["(f,g)":=show (f,g)]
        , Label "1,2" :<=>: (start i == end f) :?> Params ["(i,f)":=show (i,f)]
        ]
relFactorMDiagram d@(FactorMDiagram (Epi _) _) = relFactorMDiagram d' where
  Contravariant2 i   = toDualOpMlt 
  SDualBi (Left1 d') = amapF i (SDualBi (Right1 d))

  
--------------------------------------------------------------------------------
-- relFactorM -

-- | validating a 'FactorM'.
relFactorM :: Multiplicative x => FactorMDiagram m x -> Statement
relFactorM (FactorMDiagram (Mono i) (f,g))
  = ((f /= g) :?> Params []) :=> (i * f /= i * g) :?> Params ["(f,g)":=show (f,g)]
  -- we use this condition to avoid a lot of denied permisses!
relFactorM fd@(FactorMDiagram (Epi _) _) = relFactorM fd' where
  Contravariant2 i    = toDualOpMlt 
  SDualBi (Left1 fd') = amapF i (SDualBi (Right1 fd))

instance (Multiplicative x, XStandardOrtOrientation x) => Validable (FactorM m x) where
  valid m = Label "FactorM" :<=>: Forall (xD m) relFactorM where
    xD = xoFactorMDiagram xStandardOrtOrientation

