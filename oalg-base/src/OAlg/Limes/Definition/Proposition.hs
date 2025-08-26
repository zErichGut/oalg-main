
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
  , XEligibleCone(..), XStandardEligibleCone(..)
  , xEligibleConeOrnt, coXEligibleCone
  , xecMapS, xecMapCnt
  
  , XEligibleConeFactor(..), XStandardEligibleConeFactor(..)
  , xEligibleConeFactorOrnt, coXEligibleConeFactor
  , xecfOrtSite
  
  ) where

import Control.Monad

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Definition
import OAlg.Hom.Multiplicative

import OAlg.Limes.Cone

import OAlg.Limes.Definition.Core
import OAlg.Limes.Definition.Duality

--------------------------------------------------------------------------------
-- XEligibleCone -

-- | random variable for eligible cones for a given limes.
data XEligibleCone c s p d t n m x
  = XEligibleCone (LimesG c s p d t n m x -> X (Cone s p d t n m x))

--------------------------------------------------------------------------------
-- XStandardEligibleCone -

-- | standard random variable for eligible cones.
class XStandardEligibleCone c s p d t n m x where
  xStandardEligibleCone :: XEligibleCone c s p d t n m x

--------------------------------------------------------------------------------
-- Duality - XEligibleCone -

type instance Dual1 (XEligibleCone c s p d t n m) = XEligibleCone c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- xecMapCov -

-- | mapping according to a covariant isomorphism.
xecMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XEligibleCone c s p d t n m x -> XEligibleCone c s p d t n m y
xecMapCov (Covariant2 i@(Inv2 t _)) (XEligibleCone xec) = XEligibleCone xec' where
  xec' l' = xc' where
    l = lmMapCov (Covariant2 (inv2 i)) l'

    xc' = do
      c <- xec l
      let SDualBi (Right1 (ConeG c')) = amapF t (SDualBi (Right1 (ConeG c))) in return c'

--------------------------------------------------------------------------------
-- xecMapCnt -

-- | mapping according to a contravariant isomorphism.
xecMapCnt ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> XEligibleCone c s p d t n m x -> Dual1 (XEligibleCone c s p d t n m) y
xecMapCnt (Contravariant2 i@(Inv2 t _)) (XEligibleCone xec) = XEligibleCone xec' where
  xec' l' = xc' where
    l = lmMapCnt (Contravariant2 (inv2 i)) l'

    xc' = do
      c <- xec l
      let SDualBi (Left1 (ConeG c')) = amapF t (SDualBi (Right1 (ConeG c))) in return c'

--------------------------------------------------------------------------------
-- xecMapS -

xecMapS ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Inv2 h x y
  -> SDualBi (XEligibleCone c s p d t n m) x -> SDualBi (XEligibleCone c s p d t n m) y
xecMapS = vmapBi xecMapCov xecMapCov xecMapCnt xecMapCnt 

--------------------------------------------------------------------------------
-- coXEligibleCone -

-- | random variable for eligible cones over 'Op'.
coXEligibleCone ::
  ( Multiplicative x
  , NaturalConic (HomDisjEmpty s Op) c s p d t n m
  , NaturalConic (HomDisjEmpty s Op) c s (Dual p) d (Dual t) n m
  , s ~ Mlt
  )
  => XEligibleCone c s p d t n m x
  -> XEligibleCone c s (Dual p) d (Dual t) n m (Op x)
coXEligibleCone = xecMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xEligibleConeOrnt -

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
xEligibleConeOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XEligibleCone c s p d t n m (Orientation x)
xEligibleConeOrnt = XEligibleCone . xecOrnt

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardEligibleCone c s p d t n m (Orientation x) where
  xStandardEligibleCone = xEligibleConeOrnt xStandard

--------------------------------------------------------------------------------
-- XEligibleConeFactor -

-- | random variable for eligible cones together with a eligible factor for a given limes.
data XEligibleConeFactor c s p d t n m x
  = XEligibleConeFactor (LimesG c s p d t n m x -> X (Cone s p d t n m x, x))

type instance Dual1 (XEligibleConeFactor c s p d t n m)
  = XEligibleConeFactor c s (Dual p) d (Dual t) n m
  
--------------------------------------------------------------------------------
-- XStandardEligibleConeFactor -

-- | standard random variable for eligible cone factors.
class XStandardEligibleConeFactor c s p d t n m x where
  xStandardEligibleConeFactor :: XEligibleConeFactor c s p d t n m x

--------------------------------------------------------------------------------
-- xecfMapCov -

xecfMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> XEligibleConeFactor c s p d t n m x
  -> XEligibleConeFactor c s p d t n m y
xecfMapCov (Covariant2 i@(Inv2 t _)) (XEligibleConeFactor xecf) = XEligibleConeFactor xecf' where
  xecf' l' = xcf' where
    l = lmMapCov (Covariant2 (inv2 i)) l'

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Right1 (ConeG c')) = amapG t (SDualBi (Right1 (ConeG c))) in return (c',amap t f)

--------------------------------------------------------------------------------
-- xecfMapCnt -

xecfMapCnt ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Variant2 Contravariant (Inv2 h) x y
  -> XEligibleConeFactor c s p d t n m x
  -> Dual1 (XEligibleConeFactor c s p d t n m) y
xecfMapCnt (Contravariant2 i@(Inv2 t _)) (XEligibleConeFactor xecf) = XEligibleConeFactor xecf' where
    
  xecf' l' = xcf' where
    l = lmMapCnt (Contravariant2 (inv2 i)) l'

    xcf' = do
      (c,f) <- xecf l
      let SDualBi (Left1 (ConeG cOp)) = amapG t (SDualBi (Right1 (ConeG c))) in return (cOp,amap t f)

--------------------------------------------------------------------------------
-- xecfMapS -

xecfMapS ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Inv2 h x y
  -> SDualBi (XEligibleConeFactor c s p d t n m) x -> SDualBi (XEligibleConeFactor c s p d t n m) y
xecfMapS = vmapBi xecfMapCov xecfMapCov xecfMapCnt xecfMapCnt 

--------------------------------------------------------------------------------
-- coXEligibleConeFactor -

coXEligibleConeFactor ::
  ( Multiplicative x
  , NaturalConic (HomDisjEmpty s Op) c s p d t n m
  , NaturalConic (HomDisjEmpty s Op) c s (Dual p) d (Dual t) n m  
  , s ~ Mlt
  )
  => XEligibleConeFactor c s p d t n m x
  -> XEligibleConeFactor c s (Dual p) d (Dual t) n m (Op x)
coXEligibleConeFactor = xecfMapCnt toDualOpMlt

--------------------------------------------------------------------------------
-- xEligibleConeFactorOrnt -

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
xEligibleConeFactorOrnt ::
  ( Conic c
  , Diagrammatic d
  )
  => X x -> XEligibleConeFactor c s p d t n m (Orientation x)
xEligibleConeFactorOrnt xx = XEligibleConeFactor xef where
  XEligibleCone xec = xEligibleConeOrnt xx
  xef l = amap1 (\c -> (c,elgFactorOrnt l c)) $ xec l

instance
  ( Conic c
  , Diagrammatic d
  , XStandard x
  )
  => XStandardEligibleConeFactor c s p d t n m (Orientation x) where
  xStandardEligibleConeFactor = xEligibleConeFactorOrnt xStandard

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
  => XOrtSite r x -> XEligibleConeFactor c s (ToPerspective r) d t n m x
xecfOrtSite xe@(XEnd _ _)   = XEligibleConeFactor (xecfPrjOrtSiteTo xe)
xecfOrtSite xs@(XStart _ _) = XEligibleConeFactor (xecfInjOrtSiteFrom xs)

--------------------------------------------------------------------------------
-- prpLimesFactorExist -

-- | validity according the existence of a eligible factor for a given 'LimesG'
-- and 'Cone'.
prpLimesFactorExist ::
  ( Conic c
  , Diagrammatic d
  , Show (d t n m x)
  , Eq (d t n m x)
  , Entity x
  )
  => XEligibleCone c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorExist (XEligibleCone xec) l = Prp "LimesFactorExists" :<=>:
  Forall (xec l)
    (\c -> eligibleCone l c :?> Params ["c":=show c]
           -- actually the random variable should produce eligible cones!!
           -- but the preconditions tests also the validity of xec
       :=> let f = universalFactor l c
            in And [ valid f
                   , eligibleFactor l c f :?> Params ["c":=show c, "f":=show f]
                   ]
    ) 

--------------------------------------------------------------------------------
-- prpLimesFactorUnique -

-- | validity according to the uniqueness of a eligible factor for a given 'LimesG'
-- and 'Cone'.
prpLimesFactorUnique ::
  ( Conic c, Diagrammatic d
  , Show (d t n m x)
  , Eq (d t n m x)
  , Entity x
  )
  => XEligibleConeFactor c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimesFactorUnique (XEligibleConeFactor xef) l = Prp "LimesFactorUnique" :<=>:
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
  , Entity (d t n m x)
  , Entity x
  )
  => XEligibleCone c s p d t n m x
  -> XEligibleConeFactor c s p d t n m x
  -> LimesG c s p d t n m x -> Statement
prpLimes xec xef l = Prp "Limes" :<=>:
  And [ prpLimesFactorExist xec l
      , prpLimesFactorUnique xef l
      ]
