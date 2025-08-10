
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

import OAlg.Category.Dualisable
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
import OAlg.Hom.Definition

import OAlg.Limes.Perspective

import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- ConeZeroHead -

-- | predicate for cones where the first arrow of its underlying diagram is equal to 'zero'.
data ConeZeroHead s p d t n m x where
  ConeZeroHead :: Distributive x => Cone s p d t n (m+1) x -> ConeZeroHead s p d t n (m+1) x

deriving instance Show (d t n (S m) x) => Show (ConeZeroHead s p d t n (S m) x)
deriving instance Eq (d t n (S m) x) => Eq (ConeZeroHead s p d t n (S m) x)

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
-- czMapDstCnt -

czMapMltStruct :: (HomDistributive h, NaturalDiagrammatic h d t n m)
  => Struct Dst y -> h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMltStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMlt h c)

czMapMlt :: (HomDistributive h, NaturalDiagrammatic h d t n m)
  => h x y -> ConeZeroHead Mlt p d t n m x -> ConeZeroHead Mlt p d t n m y
czMapMlt h = czMapMltStruct (tau (range h)) h

czMapDstStruct :: (HomDistributive h, NaturalDiagrammatic h d t n m)
  => Struct Dst y -> h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDstStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDst h c)

czMapDst :: (HomDistributive h, NaturalDiagrammatic h d t n m)
  => h x y -> ConeZeroHead Dst p d t n m x -> ConeZeroHead Dst p d t n m y
czMapDst h = czMapDstStruct (tau (range h)) h

czMapMltCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticSDualisable h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y
czMapMltCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapMltCnt h c)

czMapMltCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticSDualisable h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Mlt p d t n m x -> Dual1 (ConeZeroHead Mlt p d t n m) y  
czMapMltCnt h = czMapMltCntStruct (tau (range h)) h

czMapDstCntStruct ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticSDualisable h d t n m
  )
  => Struct Dst y
  -> Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y
czMapDstCntStruct Struct h (ConeZeroHead c) = ConeZeroHead (cnMapDstCnt h c)

czMapDstCnt ::
  ( HomDistributiveDisjunctive h
  , NaturalDiagrammaticSDualisable h d t n m
  )
  => Variant2 Contravariant h x y
  -> ConeZeroHead Dst p d t n m x -> Dual1 (ConeZeroHead Dst p d t n m) y  
czMapDstCnt h = czMapDstCntStruct (tau (range h)) h

--------------------------------------------------------------------------------
-- ConeZeroHead - Mlt - DualisableGBiDual1 -

instance
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammatic s o d t n m
  )
  => ReflexiveG s (->) o (ConeZeroHead Mlt p d t n m) where
  reflG s = Inv2 (czMapMlt (Covariant2 (t' . t))) (czMapMlt (Covariant2 (f . f'))) where
    Contravariant2 (Inv2 t f)   = isoO s
    Contravariant2 (Inv2 t' f') = isoO (tauO s)

instance
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammatic s o d t n m
  , DualisableDiagrammatic s o d t' n m
  , p' ~ Dual p, p ~ Dual p'
  , t' ~ Dual t, t ~ Dual t'
  )
  => DualisableGBi s (->) o (ConeZeroHead Mlt p d t n m) (ConeZeroHead Mlt p' d t' n m) where

  toDualGLft s = czMapMltCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s

  toDualGRgt s = czMapMltCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s

instance 
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammaticSelfDual1 s o d t n m
  , p ~ Dual (Dual p)
  )
  => DualisableGBiDual1 s (->) o (ConeZeroHead Mlt p d t n m)

--------------------------------------------------------------------------------
-- ConeZeroHead - Dst - DualisableGBiDual1 -

instance
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammatic s o d t n m
  )
  => ReflexiveG s (->) o (ConeZeroHead Dst p d t n m) where
  reflG s = Inv2 (czMapDst (Covariant2 (t' . t))) (czMapDst (Covariant2 (f . f'))) where
    Contravariant2 (Inv2 t f)   = isoO s
    Contravariant2 (Inv2 t' f') = isoO (tauO s)

instance
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammatic s o d t n m
  , DualisableDiagrammatic s o d t' n m
  , p' ~ Dual p, p ~ Dual p'
  , t' ~ Dual t, t ~ Dual t'
  )
  => DualisableGBi s (->) o (ConeZeroHead Dst p d t n m) (ConeZeroHead Dst p' d t' n m) where

  toDualGLft s = czMapDstCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s

  toDualGRgt s = czMapDstCnt (Contravariant2 t) where
    Contravariant2 (Inv2 t _) = isoO s

instance 
  ( TransformableDst s
  , DualisableDistributive s o
  , DualisableDiagrammaticSelfDual1 s o d t n m
  , p ~ Dual (Dual p)
  )
  => DualisableGBiDual1 s (->) o (ConeZeroHead Dst p d t n m)

--------------------------------------------------------------------------------
-- ConeZeroHead - ApplicativeG -

instance (HomDistributive h, NaturalDiagrammatic h d t n m)
  => ApplicativeG (ConeZeroHead Mlt p d t n m) h (->) where
  amapG = czMapMlt

instance (HomDistributive h, NaturalDiagrammatic h d t n m)
  => ApplicativeG (ConeZeroHead Dst p d t n m) h (->) where
  amapG = czMapDst

instance
  ( HomDistributive h
  , NaturalDiagrammaticDual1 h d t n m
  )
  => ApplicativeGDual1 (ConeZeroHead Mlt p d t n m) h (->)

instance 
  ( HomDistributive h, TransformableDst s
  , DualisableDistributive s o
  , NaturalDiagrammaticSelfDual1 h d t n m 
  , DualisableDiagrammaticSelfDual1 s o d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeZeroHead Mlt p d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

instance
  ( HomDistributive h
  , NaturalDiagrammaticDual1 h d t n m
  )
  => ApplicativeGDual1 (ConeZeroHead Dst p d t n m) h (->)

instance 
  ( HomDistributive h, TransformableDst s
  , DualisableDistributive s o
  , NaturalDiagrammaticSelfDual1 h d t n m 
  , DualisableDiagrammaticSelfDual1 s o d t n m
  , p ~ Dual (Dual p)
  )
  => ApplicativeG (SDualBi (ConeZeroHead Dst p d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = amapG h

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
  Contravariant2 (Inv2 t f) = isoOpDst
  SDualBi (Left1 c')  = amapG t (SDualBi (Right1 c))
  cz'                 = cnDiffHead c'
  SDualBi (Right1 cz) = amapG f (SDualBi (Left1 cz'))
cnDiffHead c@(ConeInjective (DiagramParallelRL _ _ _) _ _) = cz where
  Contravariant2 (Inv2 t f) = isoOpDst
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
  Contravariant2 (Inv2 t f) = isoOpDst

  SDualBi (Left1 cz') = amapG t (SDualBi (Right1 cz))
  c'                  = cnKernel cz'
  SDualBi (Right1 c)  = amapG f (SDualBi (Left1 c'))

