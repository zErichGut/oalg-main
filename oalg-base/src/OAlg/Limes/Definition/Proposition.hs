
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Definition.Proposition
-- Description : proposition for a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- proposition of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
module OAlg.Limes.Definition.Proposition
  (
    -- * Proposition
    prpLimes, prpLimesFactorExist, prpLimesFactorUnique

    -- * X
  , XGEligibleCone(..)
  , XStandardGEligibleCone(..), XStandardEligibleCone
  , xGEligibleConeOrnt, coXGEligibleCone
  , xecMapS, xecMapCnt
  , xecDiscrete
  
  , XGEligibleConeFactor(..)
  , XStandardGEligibleConeFactor(..), XStandardEligibleConeFactor
  , xGEligibleConeFactorOrnt, coXGEligibleConeFactor
  , xecfOrtSite
  
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone

import OAlg.Limes.Definition.Core
import OAlg.Limes.Definition.Duality()

--------------------------------------------------------------------------------
-- XGEligibleCone -

-- | random variable for eligible cones for a given limes.
data XGEligibleCone c s p d t n m x
  = XGEligibleCone (LimesG c s p d t n m x -> X (Cone s p d t n m x))

--------------------------------------------------------------------------------
-- XStandardGEligibleCone -

-- | standard random variable for eligible cones.
class XStandardGEligibleCone c s p d t n m x where
  xStandardGEligibleCone :: XGEligibleCone c s p d t n m x

--------------------------------------------------------------------------------
-- XStandardEligibleCone -

-- | helper class to avoid undecidable instances.
class XStandardGEligibleCone Cone s p Diagram t n m x
  => XStandardEligibleCone s p t n m x

--------------------------------------------------------------------------------
-- Duality - XGEligibleCone -

type instance Dual1 (XGEligibleCone c s p d t n m) = XGEligibleCone c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- xecMapCov -

-- | mapping according to a covariant isomorphism.
xecMapCov :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XGEligibleCone c s p d t n m x -> XGEligibleCone c s p d t n m y
xecMapCov (Covariant2 i) (XGEligibleCone xec) = XGEligibleCone xec' where
  xec' l' = xc' where
    SDualBi (Right1 l) = amapG (inv2 i) (SDualBi (Right1 l'))

    xc' = do
      c <- xec l
      let SDualBi (Right1 (ConeG c')) = amapF i (SDualBi (Right1 (ConeG c))) in return c'

--------------------------------------------------------------------------------
-- xecMapCnt -

-- | mapping according to a contravariant isomorphism.
xecMapCnt :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> XGEligibleCone c s p d t n m x -> Dual1 (XGEligibleCone c s p d t n m) y
xecMapCnt (Contravariant2 i) (XGEligibleCone xec) = XGEligibleCone xec' where
  xec' l' = xc' where
    SDualBi (Left1 l) = amapG (inv2 i) (SDualBi (Right1 l'))

    xc' = do
      c <- xec l
      let SDualBi (Left1 (ConeG c')) = amapF i (SDualBi (Right1 (ConeG c))) in return c'

--------------------------------------------------------------------------------
-- xecMapS -

xecMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y
  -> SDualBi (XGEligibleCone c s p d t n m) x -> SDualBi (XGEligibleCone c s p d t n m) y
xecMapS = vmapBi xecMapCov xecMapCov xecMapCnt xecMapCnt 

--------------------------------------------------------------------------------
-- coXGEligibleCone -

-- | random variable for eligible cones over 'Op'.
coXGEligibleCone ::
  ( Multiplicative x
  , NaturalConicBi (Inv2 (HomDisjEmpty s Op)) c s p d t n m
  , s ~ Mlt
  )
  => XGEligibleCone c s p d t n m x
  -> XGEligibleCone c s (Dual p) d (Dual t) n m (Op x)
coXGEligibleCone = xecMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xGEligibleConeOrnt -

-- | random variable of eligible 'Cone's over 'Orientation'.
xecOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> LimesG c s p d t n m (Orientation x) -> X (Cone s p d t n m (Orientation x))
xecOrnt xx (LimesProjective u _)
  = case cone u of
  ConeProjective d _ _ -> xCnPrjOrnt xx (return d)
  ConeKernel d _       -> xCnPrjDstOrnt xx (return d)
xecOrnt xx (LimesInjective u _)
  = case cone u of
  ConeInjective d _ _ -> xCnInjOrnt xx (return d)
  ConeCokernel d _    -> xCnInjDstOrnt xx (return d)
  
-- | random variable of eligible 'Cone's over 'Orientation'.
xGEligibleConeOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XGEligibleCone c s p d t n m (Orientation x)
xGEligibleConeOrnt = XGEligibleCone . xecOrnt

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardGEligibleCone c s p d t n m (Orientation x) where
  xStandardGEligibleCone = xGEligibleConeOrnt xStandard

--------------------------------------------------------------------------------
-- xecDiscrete -

-- | random variable for eligible cones over 'Discrete' diagrammtic objects
xecDiscrete ::
  ( Multiplicative x
  , Conic c
  , Diagrammatic d
  )
  => XOrtOrientation x -> XGEligibleCone c s p d Discrete n m x
xecDiscrete xo = XGEligibleCone $ xec xo where

  xArwsPrj :: XOrtOrientation x -> Point x -> FinList n (Point x) -> X (FinList n x)
  xArwsPrj xo s = xListF . amap1 (\p -> xoArrow xo (s:>p))

  xArwsInj :: XOrtOrientation x -> Point x -> FinList n (Point x) -> X (FinList n x)
  xArwsInj xo e = xListF . amap1 (\p -> xoArrow xo (p:>e))
  
  xec ::
    ( Multiplicative x
    , Conic c
    , Diagrammatic d
    , t ~ Discrete
    )
    => XOrtOrientation x -> LimesG c s p d t n m x -> X (Cone s p d t n m x)
  xec xo (LimesProjective u _) = do
    t  <- xoPoint xo
    case cone u of
      ConeProjective d _ _ -> xArwsPrj xo t (dgPoints $ diagram d) >>= return . ConeProjective d t

  xec xo (LimesInjective u _) = do
    t <- xoPoint xo
    case cone u of
      ConeInjective d _ _ -> xArwsInj xo t (dgPoints $ diagram d) >>= return . ConeInjective d t

--------------------------------------------------------------------------------
-- XGEligibleConeFactor -

-- | random variable for eligible cones together with a eligible factor for a given limes.
data XGEligibleConeFactor c s p d t n m x
  = XGEligibleConeFactor (LimesG c s p d t n m x -> X (Cone s p d t n m x, x))

type instance Dual1 (XGEligibleConeFactor c s p d t n m)
  = XGEligibleConeFactor c s (Dual p) d (Dual t) n m
  
--------------------------------------------------------------------------------
-- XStandardGEligibleConeFactor -

-- | standard random variable for eligible cone factors.
class XStandardGEligibleConeFactor c s p d t n m x where
  xStandardGEligibleConeFactor :: XGEligibleConeFactor c s p d t n m x

--------------------------------------------------------------------------------
-- XStandardEligibleCone -

-- | helper class to avoid undecidable instances.
class XStandardGEligibleConeFactor Cone s p Diagram t n m x => XStandardEligibleConeFactor s p t n m x

--------------------------------------------------------------------------------
-- xecfMapCov -

xecfMapCov :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XGEligibleConeFactor c s p d t n m x
  -> XGEligibleConeFactor c s p d t n m y
xecfMapCov (Covariant2 i) (XGEligibleConeFactor xecf) = XGEligibleConeFactor xecf' where
  xecf' l' = xcf' where
    SDualBi (Right1 l) = amapF (inv2 i) (SDualBi (Right1 l'))

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Right1 (ConeG c')) = amapF i (SDualBi (Right1 (ConeG c))) in return (c',amapf i f)

--------------------------------------------------------------------------------
-- xecfMapCnt -

xecfMapCnt :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> XGEligibleConeFactor c s p d t n m x
  -> Dual1 (XGEligibleConeFactor c s p d t n m) y
xecfMapCnt (Contravariant2 i) (XGEligibleConeFactor xecf) = XGEligibleConeFactor xecf' where
  xecf' l' = xcf' where
    SDualBi (Left1 l) = amapF (inv2 i) (SDualBi (Right1 l'))

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Left1 (ConeG cOp)) = amapG i (SDualBi (Right1 (ConeG c))) in return (cOp,amapf i f)

--------------------------------------------------------------------------------
-- xecfMapS -

xecfMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y
  -> SDualBi (XGEligibleConeFactor c s p d t n m) x -> SDualBi (XGEligibleConeFactor c s p d t n m) y
xecfMapS = vmapBi xecfMapCov xecfMapCov xecfMapCnt xecfMapCnt 

--------------------------------------------------------------------------------
-- coXGEligibleConeFactor -

coXGEligibleConeFactor ::
  ( Multiplicative x
  , NaturalConicBi (Inv2 (HomDisjEmpty s Op)) c s p d t n m
  , s ~ Mlt
  )
  => XGEligibleConeFactor c s p d t n m x
  -> XGEligibleConeFactor c s (Dual p) d (Dual t) n m (Op x)
coXGEligibleConeFactor = xecfMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xGEligibleConeFactorOrnt -

-- | gets a eligible factor for the given 'LimesG' and 'Cone'.
elgFactorOrnt :: Conic c
  => LimesG c s p d t n m (Orientation x)
  -> Cone s p d t n m (Orientation x) -> Orientation x
elgFactorOrnt l c = case cone $ universalCone l of
  ConeProjective _ t _ -> tip c :> t  
  ConeInjective _ t _  -> t :> tip c
  ConeKernel _ k       -> tip c :> start k
  ConeCokernel _ k     -> end k :> tip c

-- | random variable of eligible factors over 'Orienteation'.
xGEligibleConeFactorOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XGEligibleConeFactor c s p d t n m (Orientation x)
xGEligibleConeFactorOrnt xx = XGEligibleConeFactor xef where
  XGEligibleCone xec = xGEligibleConeOrnt xx
  xef l = amap1 (\c -> (c,elgFactorOrnt l c)) $ xec l

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardGEligibleConeFactor c s p d t n m (Orientation x) where
  xStandardGEligibleConeFactor = xGEligibleConeFactorOrnt xStandard

--------------------------------------------------------------------------------
-- xecfOrtSite -

xecfPrjOrtSiteTo :: Conic c
  => XOrtSite To x -> LimesG c s Projective d t n m x -> X (Cone s Projective d t n m x, x)
xecfPrjOrtSiteTo (XEnd _ xe) l = amap1 (cn u) $ xe $ tip u where
  u = cone $ universalCone l
    
  cn :: Cone s Projective d t n m x -> x -> (Cone s Projective d t n m x, x)
  cn (ConeProjective d _ as) f = (ConeProjective d (start f) (amap1 (*f) as), f)
  cn (ConeKernel d a) f        = (ConeKernel d (a*f),f)     

xecfInjOrtSiteFrom :: Conic c
  => XOrtSite From x -> LimesG c s Injective d t n m x -> X (Cone s Injective d t n m x, x)
xecfInjOrtSiteFrom (XStart _ xs) l = amap1 (cn u) $ xs $ tip u where
  u = cone $ universalCone l
    
  cn :: Cone s Injective d t n m x -> x -> (Cone s Injective d t n m x, x)
  cn (ConeInjective d _ as) f = (ConeInjective d (end f) (amap1 (f*) as),f)
  cn (ConeCokernel d a) f     = (ConeCokernel d (f*a),f)

xecfOrtSite :: Conic c
  => XOrtSite r x -> XGEligibleConeFactor c s (ToPerspective r) d t n m x
xecfOrtSite xe@(XEnd _ _)   = XGEligibleConeFactor (xecfPrjOrtSiteTo xe)
xecfOrtSite xs@(XStart _ _) = XGEligibleConeFactor (xecfInjOrtSiteFrom xs)

--------------------------------------------------------------------------------
-- prpLimesFactorExist -

-- | validity according the existence of a eligible factor for a given 'LimesG'
-- and 'Cone'.
prpLimesFactorExist ::
  ( Conic c
  , Diagrammatic d
  , Show (c s p d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => XGEligibleCone c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorExist (XGEligibleCone xec) l = Prp "LimesFactorExists" :<=>:
  Forall (xec l)
    (\c -> eligibleCone l c :?> Params ["c":=show c]
           -- actually the random variable should produce eligible cones!!
           -- but the preconditions tests also the validity of xec
       :=> let f = universalFactor l c
            in And [ valid f
                   , eligibleFactor l c f :?> Params
                       [ "u":= show (universalCone l)
                       , "c":=show c
                       , "f":=show f
                       ]
                   ]
    ) 

--------------------------------------------------------------------------------
-- prpLimesFactorUnique -

-- | validity according to the uniqueness of a eligible factor for a given 'LimesG'
-- and 'Cone'.
prpLimesFactorUnique ::
  ( Conic c, Diagrammatic d
  , Entity (d t n m x)
  , Entity x
  )
  => XGEligibleConeFactor c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorUnique (XGEligibleConeFactor xef) l = Prp "LimesFactorUnique" :<=>:
  Forall (xef l)
    (\(c,x) -> And [ eligibleCone l c :?> Params []
                   , eligibleFactor l c x :?> Params []
                   ]
           :=> let f = universalFactor l c
                in (x == f) :?> Params ["c":=show c, "x'":=show x, "f":=show f]
    )

--------------------------------------------------------------------------------
-- prpLimes -

-- | validity according to 'LimesG'.
prpLimes ::
  ( Conic c
  , Diagrammatic d
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => XGEligibleCone c s p d t n m x
  -> XGEligibleConeFactor c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimes xec xef l = Prp "Limes" :<=>:
  And [ valid (universalCone l)
      , prpLimesFactorExist xec l
      , prpLimesFactorUnique xef l
      ]

--------------------------------------------------------------------------------
-- Validable -

instance
  ( Conic c, Diagrammatic d
  , XStandardGEligibleCone c s p d t n m x
  , XStandardGEligibleConeFactor c s p d t n m x
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => Validable (LimesG c s p d t n m x) where
  valid = prpLimes xStandardGEligibleCone xStandardGEligibleConeFactor

