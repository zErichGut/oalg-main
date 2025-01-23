
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Exact.Variance
-- Description : measuring the deviation of being exact.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- measuring the deviation of being exact.
module OAlg.Limes.Exact.Variance
  (
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

import OAlg.Entity.Diagram
import OAlg.Entity.Natural
import OAlg.Entity.FinList

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsZero


import OAlg.Data.Symbol

--------------------------------------------------------------------------------
-- Variance -

-- | measuring the 'deviation' of two consecutive zero-able arrows of being exact accordind to
-- the 'variance' of a 'ConsZero'.
--
-- __Properties__ Let @'Variance' t ker coker@ be in @t'Variance' __t__ __d__@ for a 'Distributive'
-- structure @__d__@, then holds:
--
-- (1) If @'end' t@ matches @'ConsZero' ('DiagramChainTo' _ _)@ then holds:
--
-- @
--                                  v              w
-- top:      end t         a <------------ b <------------ c
--             ^           ^               ^              ||
--             |           |               |              ||
--           t |           | t0 = 0        | t1 = ker v   || t2 = one c
--             |           |               |              ||
--             |           |               ^              ||
-- bottom:  start t        a'<<----------- b'<------------ c
--                           v' = coker w'         w'
-- @
--
--    (1.1) @ker@ is the kernel of @v@.
--
--    (1.2) @t1@ is the factor of the universal cone of @ker@.
--
--    (1.3) @t2@ is 'one'.
--
--    (1.4) @w'@ is the universal factor of @w '*' t2@.
--
--    (1.5) @coker@ is the cokernel of @w'@.
--
--    (1.6) @v'@ is the factor of the universal cone of @coker@.
--
--    (1.7) @t0@ is the universal arrow of @v '*' t1@ and hence 'zero'.
--
-- (2) If @'start' t@ matches @'ConsZero' ('DiagramChainFrom' _ _)@ then holds:
--
-- @
--                                  v              w
-- top:      sart t        a ------------> b ------------> c
--             |           |               |              ||
--             |           |               |              ||
--           t |           | t0 = 0        | t1 = coker v || t2 = one c
--             |           |               v              ||
--             v           v               v              ||
-- bottom:   end t         a'>-----------> b'------------> c
--                           v' = ker w'         w'
-- @
--
--    (2.1) @coker@ is the cokernel of @v@.
--
--    (2.2) @t1@ is the factor of the universal cone of @coker@.
--
--    (2.3) @t2@ is 'one'.
--
--    (2.4) @w'@ is the universal factor of @t2 '*' w@.
--
--    (2.5) @ker@ is the kernel of @w'@.
--
--    (2.6) @v'@ is the factor of the universal cone of @ker@.
--
--    (2.7) @t0@ is the universal arrow of @t1 '*' v@ and hence 'zero'.
data Variance t d
  = Variance
      (ConsZeroTrafo t N0 d)
      (Kernel N1 d)
      (Cokernel N1 d)
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Variance - Duality -

type instance Dual (Variance t d) = Variance (Dual t) (Op d)

coVariance :: Distributive d => Variance t d -> Dual (Variance t d)
coVariance (Variance t ker coker) = Variance (coConsZeroTrafo t) ker' coker' where
  ker'   = lmToOp cokrnLimesDuality coker 
  coker' = lmToOp krnLimesDuality ker

vrzFromOpOp :: Distributive d => Variance t (Op (Op d)) -> Variance t d
vrzFromOpOp (Variance t ker coker) = Variance t' ker' coker' where
  t' = cnztFromOpOp t

  ker'   = lmFromOp krnLimesDuality $ lmFromOp cokrnLimesDuality ker
  coker' = lmFromOp cokrnLimesDuality $ lmFromOp krnLimesDuality coker

coVarianceInv :: Distributive d => Dual (Dual t) :~: t -> Dual (Variance t d) -> Variance t d
coVarianceInv Refl v = vrzFromOpOp $ coVariance v

--------------------------------------------------------------------------------
-- Variance - Validable -

instance (Distributive d, XStandardOrtSiteTo d, XStandardOrtSiteFrom d)
  => Validable (Variance t d) where
  valid v@(Variance t ker coker) = Label "Variance" :<=>:
    And [ valid t
        , valid ker
        , valid coker
        , case t of
            ConsZeroTrafo _ (ConsZero (DiagramChainTo _ _)) _
              -> Label "To" :<=>: vldVarianceTo v
            ConsZeroTrafo (ConsZero (DiagramChainFrom _ _)) _ _
              -> Label "From" :<=>: vldVarianceTo $ coVariance v
        ]
    where
      vldVarianceTo :: Distributive d => Variance To d -> Statement
      vldVarianceTo (Variance t@(ConsZeroTrafo _ _ ts) ker coker)
        = And [ Label "1" :<=>: (v == uKer) :?> Params ["v":=show v]
              , Label "2" :<=>: (t1 == fKer) :?> Params ["t1":=show t1]
              , Label "3" :<=>: isOne t2 :?> Params ["t2":=show t2]
              , Label "4" :<=>: (w' == uw) :?> Params ["w'":=show w']
              , Label "5" :<=>: (w' == uCoker) :?> Params ["w'":=show w']
              , Label "6" :<=>: (v' == fCoker) :?> Params ["v'":=show v']
              , Label "7" :<=>: (t0 == uv' && isZero t0) :?> Params ["t0":=show t0]
              ]
        where
          ConsZero (DiagramChainTo _ (v:|w:|Nil))   = end t
          ConsZero (DiagramChainTo _ (v':|w':|Nil)) = start t
          t0:|t1:|t2:|Nil = ts

          ConeKernel dKer@(DiagramParallelLR _ _ (uKer:|Nil)) fKer         = universalCone ker
          ConeCokernel dCoker@(DiagramParallelRL _ _ (uCoker:|Nil)) fCoker = universalCone coker

          uw = universalFactor ker (ConeKernel dKer (w * t2))

          uv' = universalFactor coker (ConeCokernel dCoker (v * t1))

--------------------------------------------------------------------------------
-- vrcTop -

-- | the top 'ConsZero' chain in the diagram for 'Variance'.
vrcTop :: Distributive d => Variance t d -> ConsZero t N0 d
vrcTop v@(Variance d2x3 _ _)         = case d2x3 of
  ConsZeroTrafo _ e _               -> case e of
    ConsZero (DiagramChainTo _ _)   -> e
    ConsZero (DiagramChainFrom _ _) -> coConsZeroInv Refl $ vrcTop $ coVariance v
    
--------------------------------------------------------------------------------
-- vrcBottom -

-- | the bottom 'ConsZero' chain in the diagram for 'Variance'.
vrcBottom :: Distributive d => Variance t d -> ConsZero t N0 d
vrcBottom v@(Variance d2x3 _ _)      = case d2x3 of
  ConsZeroTrafo s _ _               -> case s of
    ConsZero (DiagramChainTo _ _)   -> s
    ConsZero (DiagramChainFrom _ _) -> coConsZeroInv Refl $ vrcBottom $ coVariance v

--------------------------------------------------------------------------------
-- variance -

-- | the variance of a 'ConsZero'.
variance :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t N0 d -> Variance t d
variance kers cokers e@(ConsZero (DiagramChainTo _ (v:|w:|Nil)))
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

variance kers cokers c@(ConsZero (DiagramChainFrom _ _))
  = coVarianceInv Refl $ variance kers' cokers' $ coConsZero c where

  kers' = lmsToOp cokrnLimitsDuality cokers
  cokers' = lmsToOp krnLimitsDuality kers

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
-- deviations -

deviations :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZero t n d -> Diagram Discrete (n+1) N0 d
deviations kers cokers = DiagramDiscrete . amap1 deviation . variances kers cokers

--------------------------------------------------------------------------------
-- VarianceTrafo -

-- | transformation between two 'Variance', i.e. the 'ConsZeroTrafo' between its top 'ConeZero' chains
-- given by 'vrcTop' (see diagram for 'Variance'). Such a transformation give rise to a
-- 'ConsZeroTrafo' betweeen its bottom 'ConsZero' chains, given by 'vrctBottom'.
--
-- __Property__ Let @t@ be in @'VarianceTrafo' __t__ __d__@ for a 'Distributive' structure @__d__@,
-- then holds: @t@ is 'valid' iff @'vrctTop' t@ is 'valid'.
data VarianceTrafo t d = VarianceTrafo (Variance t d) (Variance t d) (FinList N3 d)

--------------------------------------------------------------------------------
-- vrctTop -

-- | the induced 'ConsZeroTrafo' between the top 'ConsZero' chains (see diagram for 'Variance').
vrctTop :: VarianceTrafo t d -> ConsZeroTrafo t N0 d
vrctTop = error "nyi"

--------------------------------------------------------------------------------
-- deviatinsTrafo -

-- | the induced transformation of 'deviations'.
deviationsTrafo :: Distributive d
  => Kernels N1 d -> Cokernels N1 d -> ConsZeroTrafo t n d -> Transformation Discrete (n+1) N0 d
deviationsTrafo = error "nyi"

--------------------------------------------------------------------------------

cFrom = ConsZero (DiagramChainFrom A ((A:>B):|(B:>C):|Nil))
cTo = ConsZero (DiagramChainTo A ((B:>A):|(C:>B):|Nil))

v = variance (kernelsOrnt X) (cokernelsOrnt Y) cFrom
