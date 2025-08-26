
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Limes.Definition.Core
-- Description : basice definition of a limes over a digrammatic object.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basic definition of a 'Limes' over a 'Diagrammatic' object yielding a 'Conic' object.
module OAlg.Limes.Definition.Core
  (
    -- * Limes
    Limes, LimesG(..)
  , universalCone, universalFactor
  , eligibleCone, eligibleFactor

    -- * Constructions
  , lmMltPrjOrnt, lmMltInjOrnt

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Entity.Diagram
import OAlg.Entity.FinList

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative

import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive

import OAlg.Limes.Cone

--------------------------------------------------------------------------------
-- LimesG -

-- | limes of a 'Diagrammatic' object, i.e. a distinguished 'Conic' object over a the underlying
-- 'diagrammaticObject' having the following /universal/ property
--
-- __Property__ Let @'Conic' __c__@, @'Diagrammatic' ___d__@, @'Multiplicative' __x__@ and
-- @l@ in @'LimesG' __s p c d t n m x__@ then holds:
-- Let @u = 'universalCone' l@ in
--
-- (1) For all @c@ in @'Cone' __s p d t n m x__@ with
-- @'eligibleCone' l c@ holds: Let @f = 'universalFactor' l c@ in
--
--     (1) @'eligibleFactor' l c f@.
--
--     (2) For all @x@ in @__x__@ with @'eligibleFactor' l c x@ holds: @x '==' f@.
--
-- __Note__
--
-- (1) #Nt1#As the function @'universalFactor' l@ for a given limes @l@ is uniquely
-- determined by the underlying cone of @l@, it is permissible to test equality of two
-- limits just by there underling cones. In every computation equal limits
-- can be safely replaced by each other.
--
-- (2) It is not required that the evaluation of universal factor on a non eligible cone
--  yield an exception! The implementation of the general algorithms for limits do not
--  check for eligibility.
data LimesG c s p d t n m x where
  LimesProjective :: c s Projective d t n m x -> (Cone s Projective d t n m x -> x)
                  -> LimesG c s Projective d t n m x
                  
  LimesInjective  :: c s Injective  d t n m x -> (Cone s Injective  d t n m x -> x)
                  -> LimesG c s Injective  d t n m x

--------------------------------------------------------------------------------
-- Limes -

-- | limes for 'Cone's over 'Diagram's.
type Limes s p = LimesG Cone s p Diagram

--------------------------------------------------------------------------------
-- universalCone -

-- | the unviersal 'Conic' object given by the 'LimesG'.
universalCone :: LimesG c s p d t n m x -> c s p d t n m x
universalCone (LimesProjective u _) = u
universalCone (LimesInjective  u _) = u

--------------------------------------------------------------------------------
-- universalFactor -

-- | the unviersal factor given by the 'LimesG'.
universalFactor :: LimesG c s p d t n m x -> Cone s p d t n m x -> x
universalFactor (LimesProjective _ f) = f
universalFactor (LimesInjective  _ f) = f

--------------------------------------------------------------------------------
-- eligibleCone -

-- | eligibility of a 'Cone' according to the given 'LimesG'.
eligibleCone :: (Conic c, Eq (d t n m x)) => LimesG c s p d t n m x -> Cone s p d t n m x -> Bool
eligibleCone l c = (diagrammaticObject $ cone $ universalCone l) == diagrammaticObject c

--------------------------------------------------------------------------------
-- cnEligibleFactorDgm -

-- | eligibility of a factor according to the given 'Cones' over 'Diagram's,
cnEligibleFactorDgm :: Cone s p Diagram t n m x -> Cone s p Diagram t n m x -> x ->  Bool
cnEligibleFactorDgm (ConeProjective _ a as) (ConeProjective _ b bs) x
  = orientation x == b:>a && comPrj x as bs where
    comPrj :: Multiplicative x => x -> FinList n x -> FinList n x -> Bool
    comPrj _ Nil Nil         = True
    comPrj x (a:|as) (b:|bs) = a*x == b && comPrj x as bs
    
cnEligibleFactorDgm a@(ConeInjective d _ _) b x = case dgTypeRefl d of
  Refl -> cnEligibleFactorDgm a' b' x' where
    Contravariant2 (Inv2 t _) = toDualOpMlt
  
    SDualBi (Left1 a') = cnMapS t (SDualBi (Right1 a))
    SDualBi (Left1 b') = cnMapS t (SDualBi (Right1 b))
    x'                 = amap  t x

cnEligibleFactorDgm (ConeKernel _ a) (ConeKernel _ b) x
  = orientation x == start b :> start a && a*x == b

cnEligibleFactorDgm a@(ConeCokernel d _) b x = case dgTypeRefl d of
  Refl -> cnEligibleFactorDgm a' b' x' where
    Contravariant2 (Inv2 t _) = toDualOpDst
  
    SDualBi (Left1 a') = cnMapS t (SDualBi (Right1 a))
    SDualBi (Left1 b') = cnMapS t (SDualBi (Right1 b))
    x'                 = amap  t x
    
--------------------------------------------------------------------------------
-- cnEligibleFactor -

-- | eligibility of a factor according to the given 'Cones' over 'Diagrammatic' objects,
--
-- __Property__ Let @x@ be in @__x__@ and
-- @a@, @b@ in @'Cone' __s p d t n m x__@ with
-- @'diagrammaticObject' a '==' 'diagrammaticObjet' b@, then holds:
-- 
-- (1) If @__p__@ is equal to __'Projective'__ then holds:
-- @'cnEligibleFactor' a b x@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' b ':>' 'tip' a@.
--
--     (2) @ai v'*' x '==' bi@ for all @ai@ in @'shell' a@ and @bi@ in @'shell' b@.
--
-- (2) If @__p__@ is equal to __'Injective'__ then holds:
-- @'cnEligibleFactor' a b x@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' a ':>' 'tip' b@.
--
--     (2) @x v'*' ai '==' bi@ for all @ai@ in @'shell' a@ and @bi@ in @'shell' b@.
cnEligibleFactor :: Diagrammatic d
  => Cone s p d t n m x -> Cone s p d t n m x -> x ->  Bool
cnEligibleFactor a b = cnEligibleFactorDgm (coneDiagram a) (coneDiagram b)
-- we map a an b via coneDiagram in order to apply Op-duality for cones over diagrams.
-- otherwise you would have to stipulate a duality for the abstract diagrammatic
-- object!

--------------------------------------------------------------------------------
-- eligibleFactor -

-- | eligibility of a factor according to the given 'LimesG' and 'Cone',
eligibleFactor :: (Conic c, Diagrammatic d)
  => LimesG c s p d t n m x -> Cone s p d t n m x -> x -> Bool
eligibleFactor l = cnEligibleFactor (cone $ universalCone l)

--------------------------------------------------------------------------------
-- lmMltPrjOrnt -

-- | projective limes on oriented structures.
lmMltPrjOrnt :: (Entity p, x ~ Orientation p)
  => p -> Diagram t n m x -> Limes Mlt Projective t n m x
lmMltPrjOrnt t d = LimesProjective l u where
    l = cnPrjOrnt t d
    u (ConeProjective _ x _) = x:>t

--------------------------------------------------------------------------------
-- lmMltInjOrnt -

-- | injective limes on oriented structures.
lmMltInjOrnt :: (Entity p, x ~ Orientation p)
  => p -> Diagram t n m x -> Limes Mlt Injective t n m x
lmMltInjOrnt t d = LimesInjective l u where
    l = cnInjOrnt t d
    u (ConeInjective _ x _) = t:>x

{-
--------------------------------------------------------------------------------
-- LimesG - Dual -

type instance Dual1 (LimesG c s p d t n m) = LimesG c s (Dual p) d (Dual t) n m

--------------------------------------------------------------------------------
-- lmMapCov -

lmMapCov :: NaturalConic h c s p d t n m
  => Variant2 Covariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> LimesG c s p d t n m y
lmMapCov (Covariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Right1 (ConeG c')))
lmMapCov (Covariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Right1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))  
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Right1 (ConeG c')))

--------------------------------------------------------------------------------
-- lmMapCnt

lmMapCnt :: NaturalConic h c s p d t n m
  => Variant2 Contravariant (Inv2 h) x y
  -> LimesG c s p d t n m x -> Dual1 (LimesG c s p d t n m) y
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesProjective uc uf)
  = LimesInjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amap1 t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Left1 (ConeG c')))
lmMapCnt (Contravariant2 (Inv2 t f)) (LimesInjective uc uf)
  = LimesProjective uc' uf' where
  SDualBi (Left1 (ConeG uc')) = amapF t (SDualBi (Right1 (ConeG uc)))
  uf' c' = amap t (uf c) where
    SDualBi (Right1 (ConeG c)) = amapF f (SDualBi (Left1 (ConeG c')))

--------------------------------------------------------------------------------
-- lmMapS -

lmMapS ::
  ( NaturalConic h c s p d t n m
  , NaturalConic h c s (Dual p) d (Dual t) n m
  )
  => Inv2 h x y -> SDualBi (LimesG c s p d t n m) x -> SDualBi (LimesG c s p d t n m) y
lmMapS = vmapBi lmMapCov lmMapCov lmMapCnt lmMapCnt

--------------------------------------------------------------------------------
-- FunctorialG -

instance NaturalConicBi h c s p d t n m
  => ApplicativeG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->) where
  amapG = lmMapS

instance NaturalConicBi h c s p d t n m
  => FunctorialG (SDualBi (LimesG c s p d t n m)) (Inv2 h) (->)

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


{-
       let f = universalFactor l c
            in And [ valid f
                   , eligibleCone l c :?> Params []
                     :=> eligibleFactor l c f :?> Params ["c":=show c, "f":=show f]
                   ]
-}
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

-}

