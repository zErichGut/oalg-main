
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Deviation
-- Description : measuring the deviation of exactness.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- measuring the deviation exactness.
module OAlg.Limes.Exact.Deviation
  (

    -- * Variance
    Variance(..)-- , variances, variance
  -- , vrcTop, vrcBottom
{-
    -- * Deviation
    Deviation, deviations, deviation

    -- * Deviation Trafo
  , DeviationTrafo, deviationTrafos, deviationTrafo


    -- ** Duality
  , coVariance, coVarianceInv, vrcFromOpOp

    -- * Variance Trafo
  , VarianceTrafo(..), varianceTrafos, varianceTrafo
  , vrctTop, vrctBottom

    -- ** Duality
  , coVarianceTrafo, coVarianceTrafoInv, vrctFromOpOp

    -- * Proposition
  , prpDeviationOrntSymbol
-}
  ) where

import Data.Typeable
import Data.List as L ((++))

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice

import OAlg.Hom.Definition
import OAlg.Hom.Distributive

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero


import OAlg.Data.Symbol


--------------------------------------------------------------------------------
-- Variance -

-- | measuring the 'deviation' of a consecutive zero-able chain of being exact accordind to
-- the 'variance'.
--
-- __Properties__ Let @'Variance' c vs@ be in @t'Variance' __t k c d n x__@ for a 'Distributive'
-- structure @__x__@, then
-- for all @(ker 0, coker 0), (ker 1, coker 1) .. (ker i,coker i) .. (ker n,coker n)@ in @vs@,
-- and @d 0, d 1 .. d i, d (i+1) .. d (n+1)@ in @'cnzArrows' t@ holds:
--
-- (1) If @t@ matches @'ConsecutiveZero' ('DiagramChainTo' _ _)@ then holds (see diagram below):
--
--     (1) @ker i@ is a kernel of @d i@.
--
--     (2) @coker i@ is a cokernel of @d' (i+1)@, where @d' (i+1)@ is the universal factor given
--     by @ker i@ and @d (i+1)@.
--
-- @
--                d i          d (i+1)               
-- c :  ... a <------------ b <------------ c ...
--                          ^              || 
--                          |              || 
--                          | ker i        || one
--                          |              || 
--                          ^              || 
--          a'<<----------- b'<------------ c 
--               coker i        d' (i+1)
-- @
--
-- (2) If @t@ matches @'ConsecutiveZero' ('DiagramChainFrom' _ _)@ then holds (see diagram below):
--
--     (1) @coker i@ is a cokernel of @d i@.
--
--     (2) @ker i@ is a kernel of @d' (i+1)@, where @d' (i+1)@ is the universal factor given
--     by @coker i@ and @d (i+1)@.
--
-- @
--                d i          d (i+1)               
-- c :  ... a ------------> b ------------> c ...
--                          v              || 
--                          |              || 
--                          | coker i      || one
--                          v              || 
--                          v              || 
--          a'>>----------> b'------------> c 
--               ker i          d' (i+1)
-- @
data Variance t k c d n x where
  Variance
    :: ConsecutiveZero t n x
    -> FinList (n+1) (KernelG k d N1 x, CokernelG c d N1 x)
    -> Variance t k c d n x

--------------------------------------------------------------------------------
-- vrcMapCov -

vrcMapCov ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Covariant (Inv2 h) x y -> Variance t k c d n x -> Variance t k c d n y
vrcMapCov i (Variance c vs) = Variance c' vs' where
  c'  = cnzMapCov i c
  vs' = amap1 (\(ker,coker) -> (lmMapCov i ker, lmMapCov i coker)) vs

--------------------------------------------------------------------------------
-- vrcMapCnt -

vrcMapCnt ::
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  )
  => Variant2 Contravariant (Inv2 h) x y -> Variance t k c d n x -> Variance (Dual t) c k d n y
vrcMapCnt i (Variance c vs) = Variance c' vs' where
  c'  = cnzMapCnt i c
  vs' = amap1 (\(ker,coker) -> (lmMapCnt i coker, lmMapCnt i ker)) vs

--------------------------------------------------------------------------------
-- Duality -

type instance Dual1 (Variance t k c d n) = Variance (Dual t) c k d n

--------------------------------------------------------------------------------
-- vrcMapS -

vrcMapS :: 
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConicBi (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConicBi (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  , t ~ Dual (Dual t)
  )
  => Inv2 h x y -> SDualBi (Variance t k c d n) x  -> SDualBi (Variance t k c d n) y
vrcMapS = vmapBi vrcMapCov vrcMapCov vrcMapCnt vrcMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) k Dst Injective d (Parallel RightToLeft) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  , NaturalConic (Inv2 h) c Dst Projective d (Parallel LeftToRight) N2 N1
  , t ~ Dual (Dual t)

  )
  => ApplicativeG (SDualBi (Variance t k c d n)) (Inv2 h) (->) where
  amapG = vrcMapS

instance
  ( HomDistributiveDisjunctive h
  , CategoryDisjunctive h
  , NaturalConic (Inv2 h) k Dst Projective d (Parallel LeftToRight) N2 N1
  , NaturalConic (Inv2 h) k Dst Injective d (Parallel RightToLeft) N2 N1
  , NaturalConic (Inv2 h) c Dst Injective d (Parallel RightToLeft) N2 N1
  , NaturalConic (Inv2 h) c Dst Projective d (Parallel LeftToRight) N2 N1
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (Variance t k c d n)) (Inv2 h) (->)

--------------------------------------------------------------------------------
-- vrcHead -

vrcHead :: Distributive x => Variance t k c d n x -> Variance t k c d N0 x
vrcHead (Variance c vs) = Variance (cnzHead c) (head vs:|Nil)

--------------------------------------------------------------------------------
-- vrcTail -

vrcTail :: Distributive x => Variance t k c d (n+1) x -> Variance t k c d n x
vrcTail (Variance c vs) = Variance (cnzTail c) (tail vs)

--------------------------------------------------------------------------------
-- prpVariance -

relVarianceTo ::
  ( Distributive x
  
    -- d
  , Diagrammatic d
  , Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)

    -- k
  , Conic k
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)

    -- c
  , Conic c
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> N -> Variance To k c d n x -> Statement
relVarianceTo xeck xecfk xecc xecfc i
  v@(Variance c@(ConsecutiveZero (DiagramChainTo _ (f:|g:|ds))) ((ker,coker):|_))
  = And [ valid c
        , Label "ker"   :<=>: prpLimes xeck xecfk ker
        , Label "coker" :<=>: prpLimes xecc xecfc coker        
        , Label "1" :<=>: (kernelDiagram f == diagram (universalDiagram ker))
                            :?> Params [("d " L.++ show i):=show f, ("ker" L.++ show i):=show ker]
        , Label "2" :<=>: (cokernelDiagram g' == diagram (universalDiagram coker))
                            :?> Params [ ("d' " L.++ show i'):=show g'
                                       , ("coker" L.++ show i):=show coker
                                       ]
        , case ds of
            Nil    -> SValid
            _ :| _ -> relVarianceTo xeck xecfk xecc xecfc i' (vrcTail v)
                        

        ] where g' = universalFactor ker (ConeKernel (universalDiagram ker) g)
                i' = succ i

relVariance ::
  ( Distributive x

    -- d
  , Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)  
  , Entity (d (Parallel LeftToRight) N2 N1 (Op x))
  , Entity (d (Parallel RightToLeft) N2 N1 (Op x))

    -- k
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , NaturalConic (IsoO Dst Op) k Dst Projective d (Parallel LeftToRight) N2 N1
  
  , Object (k Dst Injective d (Parallel RightToLeft) N2 N1 (Op x))
  , NaturalConic (IsoO Dst Op) k Dst Injective d (Parallel RightToLeft) N2 N1
  
    -- c
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , NaturalConic (IsoO Dst Op) c Dst Injective d (Parallel RightToLeft) N2 N1

  , Object (c Dst Projective d (Parallel LeftToRight) N2 N1 (Op x))  
  , NaturalConic (IsoO Dst Op) c Dst Projective d (Parallel LeftToRight) N2 N1
  
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> Variance t k c d n x -> Statement
relVariance xeck xecfk xecc xecfc v@(Variance (ConsecutiveZero (DiagramChainTo _ _)) _)
  = relVarianceTo xeck xecfk xecc xecfc 0 v

relVariance xeck xecfk xecc xecfc v@(Variance (ConsecutiveZero (DiagramChainFrom _ _)) _)
  = relVarianceTo xeck' xecfk' xecc' xecfc' 0 v' where
  Contravariant2 i       = toDualOpDst
  
  SDualBi (Left1 v')     = vrcMapS i (SDualBi (Right1 v))
  
  SDualBi (Left1 xeck')  = xecMapS i (SDualBi (Right1 xecc))
  SDualBi (Left1 xecc')  = xecMapS i (SDualBi (Right1 xeck))
  SDualBi (Left1 xecfk') = xecfMapS i (SDualBi (Right1 xecfc))
  SDualBi (Left1 xecfc') = xecfMapS i (SDualBi (Right1 xecfk))
  

prpVariance ::
  ( Distributive x

    -- d
  , Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)  
  , Entity (d (Parallel LeftToRight) N2 N1 (Op x))
  , Entity (d (Parallel RightToLeft) N2 N1 (Op x))

    -- k
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , NaturalConic (IsoO Dst Op) k Dst Projective d (Parallel LeftToRight) N2 N1
  
  , Object (k Dst Injective d (Parallel RightToLeft) N2 N1 (Op x))
  , NaturalConic (IsoO Dst Op) k Dst Injective d (Parallel RightToLeft) N2 N1
  
    -- c
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , NaturalConic (IsoO Dst Op) c Dst Injective d (Parallel RightToLeft) N2 N1

  , Object (c Dst Projective d (Parallel LeftToRight) N2 N1 (Op x))  
  , NaturalConic (IsoO Dst Op) c Dst Projective d (Parallel LeftToRight) N2 N1
  
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> Variance t k c d n x -> Statement
prpVariance xeck xecfk xecc xecfc v = Prp "Variance"
  :<=>: relVariance xeck xecfk xecc xecfc v

{-
instance
  ( Distributive x

    -- d
  , Typeable d
  , Entity (d (Parallel LeftToRight) N2 N1 x)
  , Entity (d (Parallel RightToLeft) N2 N1 x)  
  , Entity (d (Parallel LeftToRight) N2 N1 (Op x))
  , Entity (d (Parallel RightToLeft) N2 N1 (Op x))

    -- k
  , Object (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , NaturalConic (IsoO Dst Op) k Dst Projective d (Parallel LeftToRight) N2 N1
  
  , Object (k Dst Injective d (Parallel RightToLeft) N2 N1 (Op x))
  , NaturalConic (IsoO Dst Op) k Dst Injective d (Parallel RightToLeft) N2 N1
  
    -- c
  , Object (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , NaturalConic (IsoO Dst Op) c Dst Injective d (Parallel RightToLeft) N2 N1

  , Object (c Dst Projective d (Parallel LeftToRight) N2 N1 (Op x))  
  , NaturalConic (IsoO Dst Op) c Dst Projective d (Parallel LeftToRight) N2 N1
  
  )
  => Validable (Variance t k c d n x) where
  valid = prpVariance xStandrdEligibleConeG xStandrdEligibleConeFactorG
                      xStandrdEligibleConeG xStandrdEligibleConeFactorG
-}                      
{-
--------------------------------------------------------------------------------
-- Variance -

-- | measuring the 'deviation' of two consecutive zero-able arrows of being exact accordind to
-- the 'variance' of a 'ConsecutiveZero'.
--
-- __Properties__ Let @'Variance' t ker coker@ be in @t'Variance' __t k c d n x__@ for a 'Distributive'
-- structure @__x__@, then holds:
--
-- (1) If @'end' t@ matches @'ConsZero' ('DiagramChainTo' _ _)@ then holds (see diagram below):
--
--      (1) @ker@ is a kernel of @v@.
--
--      (2) @t 1@ is the factor of the universal cone of @ker@.
--
--      (3) @w'@ is the universal factor given by @w@.
--
--      (4) @coker@ is a cokernel of @w'@.
--
--      (5) @v'@ is the factor of the universal cone of @coker@.
--
--      (6) @t 0@ is the universal factor given by @v '*' t 1@ and hence 'zero'.
--
--      (7) @t i@ is 'one' for @2 '<=' i@,
--
-- @
--                                  v              w               
-- top:      end t         a <------------ b <------------ c <------------ d ...
--             ^           ^               ^              ||              ||
--             |           |               |              ||              ||
--           t |           | t 0 = 0       | t 1 = ker v  || t 2 = one c  || t 3 = one d ...
--             |           |               |              ||              ||
--             |           |               ^              ||              || 
-- bottom:  start t        a'<<----------- b'<------------ c <------------ d ...
--                           v' = coker w'         w'
-- @
--
-- (2) If @'start' t@ matches @'ConsZero' ('DiagramChainFrom' _ _)@ then holds (see diagram below):
--
--      (1) @coker@ is a cokernel of @v@.
--
--      (2) @t 1@ is the factor of the universal cone of @coker@.
--
--      (3) @w'@ is the universal factor given by of @w@.
--
--      (4) @ker@ is a kernel of @w'@.
--
--      (5) @v'@ is the factor of the universal cone of @ker@.
--
--      (6) @t 0@ is the universal factor given by @t 1 '*' v@ and hence 'zero'.
--
--      (7) @t i@ is 'one' for @2 '<=' i@,
--
-- @
--                                  v              w
-- top:      sart t        a ------------> b ------------> c ------------> d ...
--             |           |               |              ||              ||
--             |           |               |              ||              ||
--           t |           | t0 = 0        | t1 = coker v || t2 = one c   || t3 = one d ...
--             |           |               v              ||              ||
--             v           v               v              ||              ||
-- bottom:   end t         a'>-----------> b'------------> c ------------> d ...
--                           v' = ker w'         w'
-- @
data Variance t k c d n x where
  Variance
    :: ConsecutiveZeroTrafo t n x
    -> KernelG k d N1 x
    -> CokernelG c d N1 x
    -> Variance t k c d n x

--------------------------------------------------------------------------------
-- prpVariance -

relVarianceTo ::
  ( Distributive x
  , Typeable n, Typeable d
  , Conic k, Conic c
  , Diagrammatic d

    -- k
  , Show (d (Parallel LeftToRight) N2 N1 x)
  , Show (k Dst Projective d (Parallel LeftToRight) N2 N1 x)
  , Eq (d (Parallel LeftToRight) N2 N1 x)
  , Validable (d (Parallel LeftToRight) N2 N1 x)
  , Validable (k Dst Projective d (Parallel LeftToRight) N2 N1 x)

    -- c
  , Show (d (Parallel RightToLeft) N2 N1 x)
  , Show (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  , Eq (d (Parallel RightToLeft) N2 N1 x)
  , Validable (d (Parallel RightToLeft) N2 N1 x)
  , Validable (c Dst Injective d (Parallel RightToLeft) N2 N1 x)
  
  )
  => XEligibleConeG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeFactorG k Dst Projective d (Parallel LeftToRight) N2 N1 x
  -> XEligibleConeG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> XEligibleConeFactorG c Dst Injective d (Parallel RightToLeft) N2 N1 x
  -> Variance To k c d n x -> Statement
relVarianceTo xeck xecfk xecc xecfc
  (Variance t@(ConsecutiveZeroTrafo (DiagramTrafo (DiagramChainTo _ _) _ _)) ker coker)
  = And [ valid t
        , Label "ker"   :<=>: prpLimes xeck xecfk ker
        , Label "coker" :<=>: prpLimes xecc xecfc coker
        , Label "1" :<=>: (kernelDiagram v == diagram (universalDiagram ker))
                            :?> Params ["v":=show v, "ker":=show ker]
        , Label "2" :<=>: (t1 == kernelFactor (universalCone ker))
                            :?> Params ["t 1":=show t1, "ker":=show ker]
        , Label "3" :<=>: (w' == universalFactor ker (ConeKernel (universalDiagram ker) w))
                            :?> Params ["w":=show w, "w'":=show w', "ker":=show ker]
        ] where
  
  ConsecutiveZeroTrafo
    (DiagramTrafo
      (DiagramChainTo _ (v':|w':|_)) -- bottom
      (DiagramChainTo _ (v :|w :|_)) -- top
      (t0:|t1:|ts)
    ) = t

-}
{-
--------------------------------------------------------------------------------
-- vrcTop -

-- | the top 'ConsZero' chain in the diagram for 'Variance'.
vrcTop :: ( Distributive d
          , OpDualisable k Dst, OpDualisable c Dst
          , OpDualityKernel k, OpDualityCokernel c
          , OpDualityKernel c, OpDualityCokernel k
          )
  => Variance t k c d -> ConsZero t N0 d
vrcTop v@(Variance d2x3 _ _)         = case d2x3 of
  ConsZeroTrafo _ e _               -> case e of
    ConsZero (DiagramChainTo _ _)   -> e
    ConsZero (DiagramChainFrom _ _) -> coConsZeroInv Refl $ vrcTop $ coVariance opdKernel opdCokernel v
    
--------------------------------------------------------------------------------
-- vrcBottom -

-- | the bottom 'ConsZero' chain in the diagram for 'Variance'.
vrcBottom :: ( Distributive d
             , OpDualisable k Dst, OpDualisable c Dst
             , OpDualityKernel k, OpDualityCokernel c
             , OpDualityKernel c, OpDualityCokernel k
             )
  => Variance t k c d -> ConsZero t N0 d
vrcBottom v@(Variance d2x3 _ _)      = case d2x3 of
  ConsZeroTrafo s _ _               -> case s of
    ConsZero (DiagramChainTo _ _)   -> s
    ConsZero (DiagramChainFrom _ _)
      -> coConsZeroInv Refl $ vrcBottom $ coVariance opdKernel opdCokernel v

--------------------------------------------------------------------------------
-- variance -

-- | the variance of a 'ConsZero'.
variance :: ( GenericKernel k d, GenericCokernel c d
            -- , GenericKernel (Dual c) (Op d), GenericCokernel (Dual k) (Op d)
            , Dualisable1 Dst k, Dualisable1 Dst c
            , Dualisable1 Dst (Dual k), Dualisable1 Dst (Dual c)
            , Reflexive1 Dst k, Reflexive1 Dst c
            , Dual (Dual k) ~ k, Dual (Dual c) ~ c
            )
  => ConsZero t N0 d -> Variance t k c d
variance e@(ConsZero (DiagramChainTo _ (v:|w:|Nil)))
  = Variance (ConsZeroTrafo s e (t0:|t1:|t2:|Nil)) vKer w'Coker where
  t2 = one $ start w

  dv   = kernelDiagram v
  vKer = gKernel dv
  t1   = kernelFactor $ gKernelUniversalCone vKer
  w'   = gKernelUniversalFactor vKer (ConeKernel dv w)

  dw'     = cokernelDiagram w'
  w'Coker = gCokernel dw'
  t0      = gCokernelUniversalFactor w'Coker (ConeCokernel dw' (v * t1))
  v'      = cokernelFactor $ gCokernelUniversalCone w'Coker
  
  s = ConsZero (DiagramChainTo (end v') (v':|w':|Nil))

{-
  = Variance (ConsZeroTrafo s e (t0:|t1:|t2:|Nil)) vKer w'Coker where
  t2 = one $ start w

  dv   = kernelDiagram v
  vKer = limes kers dv
  t1   = kernelFactor $ universalCone vKer
  w'   = universalFactor vKer (ConeKernel dv w)

  dw'     = cokernelDiagram w'
  w'Coker = limes cokers dw'
  t0      = universalFactor w'Coker (ConeCokernel dw' (v * t1))
  v'      = cokernelFactor $ universalCone w'Coker
  
  s = ConsZero (DiagramChainTo (end v') (v':|w':|Nil))
-}


variance c@(ConsZero (DiagramChainFrom _ _))
  = coVarianceInv Refl $ variance' Proxy Proxy c $ coConsZero c where
  variance' :: ( GenericKernel k d, GenericCokernel c d
               , Dualisable1 Dst k, Dualisable1 Dst c
               , Dualisable1 Dst (Dual k), Dualisable1 Dst (Dual c)
               , Dual (Dual k) ~ k
               , Dual (Dual c) ~ c
               )
    => Proxy k -> Proxy c -> ConsZero From N0 d
    -> ConsZero To N0 (Op d) -> Dual (Variance From k c d)
  variance' _ _ _ = variance


{-
variance kers cokers c@(ConsZero (DiagramChainFrom _ _))
  = coVarianceInv Refl $ variance kers' cokers' $ coConsZero c where

  kers' = lmsToOp cokrnLimitsDuality cokers
  cokers' = lmsToOp krnLimitsDuality kers
-}

--------------------------------------------------------------------------------
-- variances -

variances :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t n d -> FinList (n+1) (Variance t d)
variances kers cokers c = variance kers cokers (cnzHead c) :| case cnzArrows c of
  _:|_:|Nil  -> Nil
  _:|_:|_:|_ -> variances kers cokers (cnzTail c) 
  

--------------------------------------------------------------------------------
-- deviation -

-- | the 'deviation' of being exact, i.e. the 'Point' @a'@ in the diagram of 'Variance'.
deviation :: Distributive d => Variance t d -> Point d
deviation = head . cnzPoints . vrcBottom

--------------------------------------------------------------------------------
-- Deviation -

-- | measuring the deviations.
type Deviation n = Diagram Discrete n N0

--------------------------------------------------------------------------------
-- deviations -

-- | the induced 'Deviation's.
deviations :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t n d -> Deviation (n+1) d
deviations kers cokers = DiagramDiscrete . amap1 deviation . variances kers cokers

--------------------------------------------------------------------------------
-- VarianceTrafo -

-- | transformation between two 'Variance's, i.e. the 'ConsZeroTrafo' between its top 'ConeZero' chains
-- given by 'vrcTop' (see diagram for 'Variance'). Such a transformation give rise to a
-- 'ConsZeroTrafo' betweeen its bottom 'ConsZero' chains, given by 'vrctBottom'.
--
-- __Property__ Let @t@ be in @'VarianceTrafo' __t__ __d__@ for a 'Distributive' structure @__d__@,
-- then holds: @t@ is 'valid' iff @'vrctTop' t@ is 'valid'.
data VarianceTrafo t d = VarianceTrafo (Variance t d) (Variance t d) (FinList N3 d)

--------------------------------------------------------------------------------
-- VarianceTrafo - Duality -

type instance Dual (VarianceTrafo t d) = VarianceTrafo (Dual t) (Op d)

coVarianceTrafo :: Distributive d => VarianceTrafo t d -> Dual (VarianceTrafo t d)
coVarianceTrafo (VarianceTrafo a b fs)
  = VarianceTrafo (coVariance b) (coVariance a) (amap1 Op fs)

vrctFromOpOp :: Distributive d => VarianceTrafo t (Op (Op d)) -> VarianceTrafo t d
vrctFromOpOp (VarianceTrafo a b fs) = VarianceTrafo (vrcFromOpOp a) (vrcFromOpOp b) (amap1 fromOpOp fs)

coVarianceTrafoInv :: Distributive d
  => Dual (Dual t) :~: t -> Dual (VarianceTrafo t d) -> VarianceTrafo t d
coVarianceTrafoInv Refl = vrctFromOpOp . coVarianceTrafo

--------------------------------------------------------------------------------
-- vrctTop -

-- | the induced 'ConsZeroTrafo' between the top 'ConsZero' chains (see diagram for 'Variance').
vrctTop :: Distributive d => VarianceTrafo t d -> ConsZeroTrafo t N0 d
vrctTop (VarianceTrafo a b fs) = ConsZeroTrafo (vrcTop a) (vrcTop b) fs

--------------------------------------------------------------------------------
-- VariaceTrafo - Validable -

instance Distributive d => Validable (VarianceTrafo t d) where
  valid v = Label "VarianceTrafo" :<=>: valid (vrctTop v)
  
--------------------------------------------------------------------------------
-- vrctBottom -

-- | the induced 'ConsZeroTrafo' between the bottom 'ConsZero' chains (see diagram for 'Variance').
vrctBottom :: Distributive d => VarianceTrafo t d -> ConsZeroTrafo t N0 d
vrctBottom t@(VarianceTrafo a b fs) = case vrcTop a of
  ConsZero (DiagramChainTo _ _)    -> ConsZeroTrafo (vrcBottom a) (vrcBottom b) fs' where
    fs' = f'0 :| f'1 :| f'2 :| Nil

    _ :| f1 :| f2 :| Nil = fs

    f'2 = f2

    Variance (ConsZeroTrafo _ _ as) _ aCoker = a
    Variance (ConsZeroTrafo (ConsZero (DiagramChainTo _ bs')) _ _) bKer _ = b
    _ :|a1:|_ :|Nil = as
    b'0:|_ :|Nil = bs'

    bKerDgm = cnDiagram $ universalCone bKer
    f'1 = universalFactor bKer (ConeKernel bKerDgm (f1 * a1))

    aCokerDgm = cnDiagram $ universalCone aCoker
    f'0 = universalFactor aCoker (ConeCokernel aCokerDgm (b'0 * f'1))

  ConsZero (DiagramChainFrom _ _)  -> coConsZeroTrafoInv Refl $ vrctBottom $ coVarianceTrafo t 

--------------------------------------------------------------------------------
-- deviationTrafo -

-- | the transformation between the two given 'deviation's. 
deviationTrafo :: Distributive d => VarianceTrafo t d -> d
deviationTrafo t = f'0 where ConsZeroTrafo _ _ (f'0:|_) = vrctBottom t

--------------------------------------------------------------------------------
-- varianceTrafo -

-- | the induced 'VariancTrafo' given by a 'ConsZeroTrafo'.
--
-- __Property__ Let @t@ be in @'ConsZeroTrafo' __t__ 'N0' __d__@ for a 'Distributive' structure
-- @__d__@ and let @kers@ be in @'Kernels' 'N1' __d__@ and @cokers@ be in @'Cokernels' 'N1' __d__@,
-- then holds: @'vrctTop' ('varianceTraof' kers cokers t) '==' t@.
varianceTrafo :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t N0 d -> VarianceTrafo t d
varianceTrafo kers coker (ConsZeroTrafo a b fs) = VarianceTrafo va vb fs where
  va = variance kers coker a
  vb = variance kers coker b

--------------------------------------------------------------------------------
-- varianceTrafos -

varianceTrafos :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> FinList (n+1) (VarianceTrafo t d)
varianceTrafos kers cokers t
  = varianceTrafo kers cokers (cnztHead t) :| case cnztTrafos t of
      _:|_:|_:|Nil  -> Nil
      _:|_:|_:|_:|_ -> varianceTrafos kers cokers (cnztTail t)

--------------------------------------------------------------------------------
-- DeviationTrafo -

type DeviationTrafo n = Transformation Discrete n N0

--------------------------------------------------------------------------------
-- deviationTrafos -

-- | the induced 'DeviationTrafo's.
--
-- __Properties__ Let @t@ be in @'ConsZeroTrafo __t__ __n__ __d__@ for a 'Distributive' structure
-- @__d__@ and @kers@ be in @'Kernels' 'N1' __d__@ and @cokers@ be in @'Cokernels' 'N1' __d__@,
-- then holds:
--
-- (1) @'start' ('deviationTrafos' kers cokers t) '==' 'deviations' kers cokers ('start' t)@.
--
-- (2) @'end' ('deviationTrafos' kers cokers t) '==' 'deviations' kers cokers ('end' t)@.
--
-- __Note__ The resulting 'DeviationTrafo' dos not really depend on the choice of @kers@ and @cokers@,
-- i.e. the resulting 'DeviationTrafo' for different choices for @kers@ and @cokers@ are
-- /isomorphic/.
deviationTrafos :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> DeviationTrafo (n+1) d
deviationTrafos kers cokers t = Transformation a' b' ds where
  ds = amap1 deviationTrafo $ varianceTrafos kers cokers t
  
  a' = DiagramDiscrete $ amap1 start ds
  b' = DiagramDiscrete $ amap1 end ds

--------------------------------------------------------------------------------
-- prpDeviationTrafos -

-- | validity for the properties of 'deviationTrafos'.
prpDeviationTrafos :: (Distributive d, Typeable t, Typeable n)
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> Statement
prpDeviationTrafos kers cokers t = Prp "DeviationTrafos" :<=>:
  And [ Label "1" :<=>:
          (start ds == deviations kers cokers (start t)) :?> Params ["t":=show t]
      , Label "2" :<=>:
          (end ds == deviations kers cokers (end t)) :?> Params ["t":=show t]
      ]
  where
    ds = deviationTrafos kers cokers t
-}
--------------------------------------------------------------------------------
-- prpDeviation -

-- | validity of some properties for @__d__ ~ 'Orientation' 'Symbol'@.
prpDeviationOrntSymbol :: Statement
prpDeviationOrntSymbol = SValid
{-
prpDeviationOrntSymbol = Prp "Deviation" :<=>:
  And [ Forall (xSomeConsZeroTrafoOrnt 20)
          (\(SomeConsZeroTrafo t) -> prpDeviationTrafos kers cokers t)
      ]
  where kers   = kernelsOrnt X
        cokers = cokernelsOrnt Y
-}
