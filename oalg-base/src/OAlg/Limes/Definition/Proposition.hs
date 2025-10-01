
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
  , XEligibleConeG(..), xec
  , xecMapS, xecMapCov, xecMapCnt
  , xEligibleConeGOrnt, coXEligibleConeG
  , xecDiscrete
  , XStandardEligibleConeG(..), XStandardEligibleCone
  
  , XEligibleConeFactorG(..), xecf
  , xecfMapS, xecfMapCov, xecfMapCnt
  , xEligibleConeFactorGOrnt, coXEligibleConeFactorG
  , xecfOrtSite
  , xecfEligibleCone
  , XStandardEligibleConeFactorG(..), XStandardEligibleConeFactor
  
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
-- XEligibleConeG -

-- | random variable for eligible cones for a given limes.
data XEligibleConeG c s p d t n m x
  = XEligibleConeG (LimesG c s p d t n m x -> X (Cone s p d t n m x))

--------------------------------------------------------------------------------
-- xec -

-- | random variable of eligible cones.
xec :: XEligibleConeG c s p d t n m x -> LimesG c s p d t n m x -> X (Cone s p d t n m x)
xec (XEligibleConeG x) = x

--------------------------------------------------------------------------------
-- Duality - XEligibleConeG -

type instance Dual1 (XEligibleConeG c s p d t n m) = XEligibleConeG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- xecMapCov -

-- | mapping according to a covariant isomorphism.
xecMapCov :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XEligibleConeG c s p d t n m x -> XEligibleConeG c s p d t n m y
xecMapCov (Covariant2 i) (XEligibleConeG xec) = XEligibleConeG xec' where
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
  -> XEligibleConeG c s p d t n m x -> Dual1 (XEligibleConeG c s p d t n m) y
xecMapCnt (Contravariant2 i) (XEligibleConeG xec) = XEligibleConeG xec' where
  xec' l' = xc' where
    SDualBi (Left1 l) = amapG (inv2 i) (SDualBi (Right1 l'))

    xc' = do
      c <- xec l
      let SDualBi (Left1 (ConeG c')) = amapF i (SDualBi (Right1 (ConeG c))) in return c'

--------------------------------------------------------------------------------
-- xecMapS -

xecMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y
  -> SDualBi (XEligibleConeG c s p d t n m) x -> SDualBi (XEligibleConeG c s p d t n m) y
xecMapS = vmapBi xecMapCov xecMapCov xecMapCnt xecMapCnt 

--------------------------------------------------------------------------------
-- coXEligibleConeG -

-- | random variable for eligible cones over 'Op'.
coXEligibleConeG ::
  ( Multiplicative x
  , NaturalConicBi (Inv2 (HomDisjEmpty s Op)) c s p d t n m
  , s ~ Mlt
  )
  => XEligibleConeG c s p d t n m x
  -> XEligibleConeG c s (Dual p) d (Dual t) n m (Op x)
coXEligibleConeG = xecMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xEligibleConeGOrnt -

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
xEligibleConeGOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XEligibleConeG c s p d t n m (Orientation x)
xEligibleConeGOrnt = XEligibleConeG . xecOrnt

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardEligibleConeG c s p d t n m (Orientation x) where
  xStandardEligibleConeG = xEligibleConeGOrnt xStandard

--------------------------------------------------------------------------------
-- xecDiscrete -

-- | random variable for eligible cones over 'Discrete' diagrammtic objects
xecDiscrete ::
  ( Multiplicative x
  , Conic c
  , Diagrammatic d
  )
  => XOrtOrientation x -> XEligibleConeG c s p d Discrete n m x
xecDiscrete xo = XEligibleConeG $ xec xo where

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
-- XEligibleConeFactorG -

-- | random variable for eligible cones together with a eligible factor for a given limes.
data XEligibleConeFactorG c s p d t n m x
  = XEligibleConeFactorG (LimesG c s p d t n m x -> X (Cone s p d t n m x, x))

type instance Dual1 (XEligibleConeFactorG c s p d t n m)
  = XEligibleConeFactorG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- xecf -

-- | random variable of eligible cone factors.
xecf :: XEligibleConeFactorG c s p d t n m x -> LimesG c s p d t n m x -> X (Cone s p d t n m x,x)
xecf (XEligibleConeFactorG xcx) = xcx


--------------------------------------------------------------------------------
-- xecfMapCov -

-- | covariant mapping of 'XEligibleConeFactorG'
xecfMapCov :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XEligibleConeFactorG c s p d t n m x
  -> XEligibleConeFactorG c s p d t n m y
xecfMapCov (Covariant2 i) (XEligibleConeFactorG xecf) = XEligibleConeFactorG xecf' where
  xecf' l' = xcf' where
    SDualBi (Right1 l) = amapF (inv2 i) (SDualBi (Right1 l'))

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Right1 (ConeG c')) = amapF i (SDualBi (Right1 (ConeG c))) in return (c',amapf i f)

--------------------------------------------------------------------------------
-- xecfMapCnt -

-- | contravariant mapping of 'XEligibleConeFactorG'
xecfMapCnt :: NaturalConicBi (Inv2 h) c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> XEligibleConeFactorG c s p d t n m x
  -> XEligibleConeFactorG c s (Dual p) d (Dual t) n m y
xecfMapCnt (Contravariant2 i) (XEligibleConeFactorG xecf) = XEligibleConeFactorG xecf' where
  xecf' l' = xcf' where
    SDualBi (Left1 l) = amapF (inv2 i) (SDualBi (Right1 l'))

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Left1 (ConeG cOp)) = amapG i (SDualBi (Right1 (ConeG c))) in return (cOp,amapf i f)

--------------------------------------------------------------------------------
-- xecfMapS -

-- | mapping of 'XEligibleConeFactorG'
xecfMapS :: NaturalConicBi (Inv2 h) c s p d t n m
  => Inv2 h x y
  -> SDualBi (XEligibleConeFactorG c s p d t n m) x
  -> SDualBi (XEligibleConeFactorG c s p d t n m) y
xecfMapS = vmapBi xecfMapCov xecfMapCov xecfMapCnt xecfMapCnt 

--------------------------------------------------------------------------------
-- coXEligibleConeFactorG -

-- | the co-object of 'XEligibleConeFactorG' accordint to 'Op'.
coXEligibleConeFactorG ::
  ( Multiplicative x
  , NaturalConicBi (Inv2 (HomDisjEmpty s Op)) c s p d t n m
  , s ~ Mlt
  )
  => XEligibleConeFactorG c s p d t n m x
  -> XEligibleConeFactorG c s (Dual p) d (Dual t) n m (Op x)
coXEligibleConeFactorG = xecfMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xEligibleConeFactorGOrnt -

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
xEligibleConeFactorGOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XEligibleConeFactorG c s p d t n m (Orientation x)
xEligibleConeFactorGOrnt xx = XEligibleConeFactorG xef where
  XEligibleConeG xec = xEligibleConeGOrnt xx
  xef l = amap1 (\c -> (c,elgFactorOrnt l c)) $ xec l

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardEligibleConeFactorG c s p d t n m (Orientation x) where
  xStandardEligibleConeFactorG = xEligibleConeFactorGOrnt xStandard

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

-- | the random variable 'XEligibleConeFactorG' given be 'XOrtSite'.
xecfOrtSite :: Conic c
  => XOrtSite r x -> XEligibleConeFactorG c s (ToPerspective r) d t n m x
xecfOrtSite xe@(XEnd _ _)   = XEligibleConeFactorG (xecfPrjOrtSiteTo xe)
xecfOrtSite xs@(XStart _ _) = XEligibleConeFactorG (xecfInjOrtSiteFrom xs)

--------------------------------------------------------------------------------
-- xecfEligibleCone -

-- | the induced random variable for eligible cones.
xecfEligibleCone :: XEligibleConeFactorG c s p d t n m x -> XEligibleConeG c s p d t n m x
xecfEligibleCone (XEligibleConeFactorG xecf) = XEligibleConeG (amap1 fst . xecf)

--------------------------------------------------------------------------------
-- XStandardEligibleConeFactorG -

-- | standard random variable for eligible cone factors.
class XStandardEligibleConeFactorG c s p d t n m x where
  xStandardEligibleConeFactorG :: XEligibleConeFactorG c s p d t n m x
  
--------------------------------------------------------------------------------
-- XStandardEligibleCone -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeFactorG Cone s p Diagram t n m x => XStandardEligibleConeFactor s p t n m x

--------------------------------------------------------------------------------
-- XStandardEligibleConeG -

-- | standard random variable for eligible cones.
class XStandardEligibleConeG c s p d t n m x where
  xStandardEligibleConeG :: XEligibleConeG c s p d t n m x

--------------------------------------------------------------------------------
-- XStandardEligibleCone -

-- | helper class to avoid undecidable instances.
class XStandardEligibleConeG Cone s p Diagram t n m x
  => XStandardEligibleCone s p t n m x

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
  => XEligibleConeG c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorExist (XEligibleConeG xec) l = Prp "LimesFactorExists" :<=>:
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
  => XEligibleConeFactorG c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorUnique (XEligibleConeFactorG xef) l = Prp "LimesFactorUnique" :<=>:
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
  => XEligibleConeG c s p d t n m x
  -> XEligibleConeFactorG c s p d t n m x
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
  , XStandardEligibleConeG c s p d t n m x
  , XStandardEligibleConeFactorG c s p d t n m x
  , Show (c s p d t n m x)
  , Validable (c s p d t n m x)
  , Entity (d t n m x)
  , Entity x
  )
  => Validable (LimesG c s p d t n m x) where
  valid = prpLimes xStandardEligibleConeG xStandardEligibleConeFactorG

