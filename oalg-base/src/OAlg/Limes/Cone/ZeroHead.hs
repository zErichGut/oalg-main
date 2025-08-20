
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Cone.ZeroHead
-- Description : cones with a zero arrow. 
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- cones having a zero for its first arrow.
module OAlg.Limes.Cone.ZeroHead
  (
    ConeZeroHead(..)
  , cnZeroHead
  , cnKernel, cnCokernel
  , cnDiffHead
  ) where

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality

import OAlg.Data.Either

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Fibred
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Hom.Oriented
import OAlg.Hom.Distributive

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Definition
import OAlg.Limes.Cone.Conic

--------------------------------------------------------------------------------
-- ConeZeroHead -

-- | predicate for cones where the first arrow of its underlying diagram is equal to 'zero'.
data ConeZeroHead s p d t n m x where
  ConeZeroHead :: Distributive x => Cone s p d t n (m+1) x -> ConeZeroHead s p d t n (m+1) x

deriving instance Show (d t n (S m) x) => Show (ConeZeroHead s p d t n (S m) x)
deriving instance Eq (d t n (S m) x) => Eq (ConeZeroHead s p d t n (S m) x)

instance Conic ConeZeroHead where cone (ConeZeroHead c) = c
  
--------------------------------------------------------------------------------
-- ConeZeroHead - Validable -

instance (Diagrammatic d, Validable (d t n (S m) x))
  => Validable (ConeZeroHead s p d t n (S m) x) where
  valid (ConeZeroHead c)
    = And [ valid c
          , relIsZero $ head $ dgArrows $ diagram $ diagrammaticObject c
          ]

--------------------------------------------------------------------------------
-- ConeZeroHead - Dual -

type instance Dual1 (ConeZeroHead s p d t n m)  = ConeZeroHead s (Dual p) d (Dual t) n m 

--------------------------------------------------------------------------------
-- czMapS -

czMapMltCovStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Covariant h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMltCovStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMltCov h c)

czMapMltCov :: 
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMltCov h = czMapMltCovStruct (tau (range h)) h

czMapDstCovStruct :: 
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Covariant h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDstCovStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDstCov h c)

czMapDstCov ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDstCov h = czMapDstCovStruct (tau (range h)) h

czMapCov ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Covariant h x y -> ConeZeroHead s p d t n m x -> ConeZeroHead s p d t n m y
czMapCov h cz@(ConeZeroHead c) = case c of
  ConeProjective _ _ _        -> czMapMltCov h cz
  ConeInjective _ _ _         -> czMapMltCov h cz
  ConeKernel _ _              -> czMapDstCov h cz
  ConeCokernel _ _            -> czMapDstCov h cz
  
czMapMltCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y
czMapMltCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMltCnt h c)

czMapMltCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y  
czMapMltCnt h = czMapMltCntStruct (tau (range h)) h

czMapDstCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y
czMapDstCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDstCnt h c)

czMapDstCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y  
czMapDstCnt h = czMapDstCntStruct (tau (range h)) h

czMapCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammatic h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead s p d t n m x -> Dual1 (ConeZeroHead s p d t n m) y
czMapCnt h cz@(ConeZeroHead c) = case c of
  ConeProjective _ _ _        -> czMapMltCnt h cz
  ConeInjective _ _ _         -> czMapMltCnt h cz
  ConeKernel _ _              -> czMapDstCnt h cz
  ConeCokernel _ _            -> czMapDstCnt h cz
  
czMapS ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => h x y -> SDualBi (ConeZeroHead s p d t n m) x -> SDualBi (ConeZeroHead s p d t n m) y
czMapS = vmapBi czMapCov czMapCov czMapCnt czMapCnt

--------------------------------------------------------------------------------
-- ZeroHead - NaturalConic -

instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeZeroHead s p d t n m)) h (->) where
  amapG = czMapS
  
instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeZeroHead s p d t n m)) h (->)

instance
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeG ConeZeroHead s p d t n m)) h (->) where
  amapG h = sdbFromCncObj . amapG h . sdbToCncObj

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => FunctorialG (SDualBi (ConeG ConeZeroHead s p d t n m)) h (->)  

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG ConeZeroHead Mlt p d t n m)) (SDualBi (Cone Mlt p d t n m))

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h ConeZeroHead Mlt p d t n m

instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalTransformable h (->)
       (SDualBi (ConeG ConeZeroHead Dst p d t n m)) (SDualBi (Cone Dst p d t n m))
  
instance
  ( HomDistributiveDisjunctive h
  , FunctorialOriented h
  , NaturalDiagrammaticBi h d t n m
  , p ~ Dual (Dual p)
  )
  => NaturalConic h ConeZeroHead Dst p d t n m

--------------------------------------------------------------------------------
-- cnDiffHead -

-- | subtracts to every arrow of the underlying parallel diagram the first arrow and
-- adapts the shell accordingly.
cnDiffHead :: (Distributive a, Abelian a)
  => Cone Mlt p Diagram (Parallel d) n (m+1) a -> ConeZeroHead Mlt p Diagram (Parallel d) n (m+1) a
cnDiffHead (ConeProjective d t s) = ConeZeroHead $ case d of
  DiagramParallelLR _ _ _ -> ConeProjective (dgPrlDiffHead d) t (a:|amap1 toZero as) where a:|as = s
  DiagramParallelRL _ _ _ -> ConeProjective (dgPrlDiffHead d) t (toZero a:|as) where a:|as = s
  where toZero a = zero (root a)
cnDiffHead c@(ConeInjective (DiagramParallelLR _ _ _) _ _) = cz where
  Contravariant2 (Inv2 t f) = toDualOpDst
  SDualBi (Left1 c')  = amap1 t (SDualBi (Right1 c))
  cz'                 = cnDiffHead c'
  SDualBi (Right1 cz) = amap1 f (SDualBi (Left1 cz'))
cnDiffHead c@(ConeInjective (DiagramParallelRL _ _ _) _ _) = cz where
  Contravariant2 (Inv2 t f) = toDualOpDst
  SDualBi (Left1 c')  = amapG t (SDualBi (Right1 c))
  cz'                 = cnDiffHead c'
  SDualBi (Right1 cz) = amapG f (SDualBi (Left1 cz'))

--------------------------------------------------------------------------------
-- cnZeroHead -

-- | embedding of a cone in a distributive structure to its multiplicative cone.
cnZeroHead :: Cone Dst p Diagram t n m a -> ConeZeroHead Mlt p Diagram t n (m+1) a
cnZeroHead c@(ConeKernel _ _)   = ConeZeroHead (cnDstAdjZero c)
cnZeroHead c@(ConeCokernel _ _) = ConeZeroHead (cnDstAdjZero c)

--------------------------------------------------------------------------------
-- cnKernel -

-- | the kernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnKernel :: (p ~ Projective, t ~ Parallel LeftToRight)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnKernel (ConeZeroHead (ConeProjective d _ cs)) = case d of
  DiagramParallelLR l r as -> ConeKernel (DiagramParallelLR l r (tail as)) (head cs)

--------------------------------------------------------------------------------
-- cnCokernel

-- | the cokernel cone of a zero headed parallel cone, i.e. the inverse of 'cnZeroHead'.
cnCokernel :: (p ~ Injective, t ~ Parallel RightToLeft)
  => ConeZeroHead Mlt p Diagram t n (m+1) a -> Cone Dst p Diagram t n m a
cnCokernel cz@(ConeZeroHead _) = c where
  Contravariant2 (Inv2 t f) = toDualOpDst

  SDualBi (Left1 cz') = amap1 t (SDualBi (Right1 cz))
  c'                  = cnKernel cz'
  SDualBi (Right1 c)  = amap1 f (SDualBi (Left1 c'))

