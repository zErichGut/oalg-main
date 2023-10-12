
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}


-- | Eligible factors between cons.
module OAlg.Limes.Cone.EligibleFactor
  (
     -- * Eligible Factor
    cnEligibleFactor
  , EligibleFactor(..), elfFactorCone
  , elfMap
  
    -- ** Duality
  , coEligibleFactor, coEligibleFactorInv
  , elfFromOpOp

    -- ** X
  , xopEligibleFactor
  , XOrtPerspective(..)
  , XStandardOrtPerspective(..)
  
  , xosEligibleFactorPrj
  , xosEligibleFactorInj
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative as Mlt
import OAlg.Structure.Distributive

import OAlg.Hom.Multiplicative
import OAlg.Hom.Distributive
import OAlg.Hom.Definition

import OAlg.Limes.Perspective
import OAlg.Limes.Cone.Definition

--------------------------------------------------------------------------------
-- cnEligibleFactor -

-- | eligibility of a factor between two cones.
--
--   __Property__ Let @x@ be in __@a@__ and
--  @f@, @t@ in @'Cone' __s__ __p__ __t__ __n__ __m__ __a__@ with
--  @'cnDiagram' f '==' 'cnDiagram' t@, then holds:
-- 
--  (1) If __@p@__ is equal to __'Projective'__ then holds:
--  @'cnEligibleFactor' x f t@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' f ':>' 'tip' t@.
--
--     (1) @ti 'Mlt.*' x '==' fi@ for all @ti@ in @'shell' t@ and @fi@ in @'shell' f@.
--
--  (1) If __@p@__ is equal to __'Injective'__ then holds:
--  @'cnEligibleFactor' x f t@ is 'True' if and only if
--
--     (1) @'orientation' x '==' 'tip' f ':>' 'tip' t@.
--
--     (1) @x 'Mlt.*' ti '==' fi@ for all @ti@ in @'shell' t@ and @fi@ in @'shell' f@.
cnEligibleFactor :: a -> Cone s p t n m a -> Cone s p t n m a -> Bool
cnEligibleFactor x (ConeProjective _ f fs) (ConeProjective _ t ts)
  = orientation x == f:>t && comPrj x fs ts where
    comPrj :: Multiplicative a => a -> FinList n a -> FinList n a -> Bool
    comPrj _ Nil Nil         = True
    comPrj x (f:|fs) (t:|ts) = t*x == f && comPrj x fs ts
cnEligibleFactor x (ConeKernel _ f) (ConeKernel _ t)
  = orientation x == start f :> start t && t*x == f
cnEligibleFactor x f t = cnEligibleFactor (Op x) (coCone t) (coCone f)

--------------------------------------------------------------------------------
-- EligibleFactor -

-- | predicate for eligible factors betweem cones.
--
--   __Property__ Let @e@ be in @'EligibleFactor' __s__ __p__ __t__ __n__ __m__ __a__@
--  for a 'Multiplicative' structure __@a@__, then holds:
--
--  (1) If @e@ matches @'EligbileFactorTo' l x c@ then holds:
--  @'cnDiragram' l '==' 'cnDiagram' c@ and @'cnEligibleFactor' x c l@.
--
--  (1) If @e@ matches @'EligibleFactorFrom' l x c@ then holds:
--  @'cnDiagram' l '==' 'cnDiagram' c@ and @'cnEligibleFactor' x l c@.
data EligibleFactor s p t n m a where
  EligibleFactorTo :: Cone s Projective t n m a -> a -> Cone s Projective t n m a
    -> EligibleFactor s Projective t n m a
  EligibleFactorFrom :: Cone s Injective t n m a -> a -> Cone s Injective t n m a
    -> EligibleFactor s Injective t n m a

deriving instance Show a => Show (EligibleFactor s p t n m a)
--------------------------------------------------------------------------------
-- elfFactorCone -

elfFactorCone :: EligibleFactor s p t n m a -> (a,Cone s p t n m a)
elfFactorCone (EligibleFactorTo _ x c)   = (x,c)
elfFactorCone (EligibleFactorFrom _ x c) = (x,c)

--------------------------------------------------------------------------------
-- elfMap -

elfMapMlt :: Hom Mlt h
  => h a b -> EligibleFactor Mlt p t n m a -> EligibleFactor Mlt p t n m b
elfMapMlt h elf = case elf of
  EligibleFactorTo l x c   -> EligibleFactorTo (cnMapMlt h l) (h$x) (cnMapMlt h c)
  EligibleFactorFrom l x c -> EligibleFactorFrom (cnMapMlt h l) (h$x) (cnMapMlt h c)

elfMapDst :: Hom Dst h
  => h a b -> EligibleFactor Dst p t n m a -> EligibleFactor Dst p t n m b
elfMapDst h elf = case elf of
  EligibleFactorTo l x c   -> EligibleFactorTo (cnMapDst h l) (h$x) (cnMapDst h c)
  EligibleFactorFrom l x c -> EligibleFactorFrom (cnMapDst h l) (h$x) (cnMapDst h c)
  
elfMap :: Hom s h
  => h a b -> EligibleFactor s p t n m a -> EligibleFactor s p t n m b
elfMap h elf@(EligibleFactorTo l _ _) = case l of
  ConeProjective _ _ _ -> elfMapMlt h elf  
  ConeKernel _ _       -> elfMapDst h elf  
elfMap h elf@(EligibleFactorFrom l _ _) = case l of  
  ConeInjective _ _ _  -> elfMapMlt h elf  
  ConeCokernel _ _     -> elfMapDst h elf


--------------------------------------------------------------------------------
-- EligibleFactor - Duality -

type instance Dual (EligibleFactor s p t n m a)
  = EligibleFactor s (Dual p) (Dual t) n m (Op a)
  
coEligibleFactor :: EligibleFactor s p t n m a -> Dual (EligibleFactor s p t n m a)
coEligibleFactor (EligibleFactorTo l x c) = EligibleFactorFrom l' (Op x) c' where
  l' = coCone l
  c' = coCone c
coEligibleFactor (EligibleFactorFrom l x c) = EligibleFactorTo l' (Op x) c' where
  l' = coCone l
  c' = coCone c

elfFromOpOp :: ConeStruct s a
  -> EligibleFactor s p t n m (Op (Op a)) -> EligibleFactor s p t n m a
elfFromOpOp ConeStructMlt = elfMapMlt isoFromOpOpMlt
elfFromOpOp ConeStructDst = elfMapDst isoFromOpOpDst

coEligibleFactorInv :: ConeStruct s a -> Dual (Dual p) :~: p -> Dual (Dual t) :~: t
  -> Dual (EligibleFactor s p t n m a) -> EligibleFactor s p t n m a
coEligibleFactorInv cs Refl Refl = elfFromOpOp cs . coEligibleFactor

--------------------------------------------------------------------------------
-- EligibleFactor - Validable -

instance Oriented a => Validable (EligibleFactor s p t n m a) where
  valid (EligibleFactorTo l x c) = Label "EligibleFactorTo" :<=>:
    And [ valid l
        , valid x
        , valid c
        , Label "diagram" :<=>:
            (cnDiagram l == cnDiagram c):?>Params["l":=show l,"c":=show c]
        , Label "eligible" :<=>:
            (cnEligibleFactor x c l):?>Params["x":=show x,"l":=show l,"c":=show c]
        ] 
  valid elf@(EligibleFactorFrom _ _ _) = valid (coEligibleFactor elf)

--------------------------------------------------------------------------------
-- xosEligibleFactorPrj -

xosEligibleFactorPrj :: XOrtSite To a -> Cone s Projective t n m a
  -> X (EligibleFactor s Projective t n m a)
xosEligibleFactorPrj (XEnd _ xe) l
  = xe (tip l) >>= return . elf l where
    elf :: Cone s Projective t n m a -> a -> EligibleFactor s Projective t n m a
    elf l@(ConeProjective d _ cs) x = EligibleFactorTo l x (ConeProjective d (start x) cs')
      where cs' = fmap (*x) cs
    elf l@(ConeKernel d k) x = EligibleFactorTo l x (ConeKernel d (k*x))

--------------------------------------------------------------------------------
-- xosEligibleFactorInj -

xosEligibleFactorInj :: ConeStruct s a -> Dual (Dual t) :~: t
  -> XOrtSite From a -> Cone s Injective t n m a
  -> X (EligibleFactor s Injective t n m a)
xosEligibleFactorInj cs rt xos
  = fmap (coEligibleFactorInv cs Refl rt) . xosEligibleFactorPrj (coXOrtSite xos) . coCone

--------------------------------------------------------------------------------
-- XOrtPerspective -

data XOrtPerspective p a where
  XOrtProjective :: XOrtSite To a -> XOrtPerspective Projective a
  XOrtInjective :: XOrtSite From a -> XOrtPerspective Injective a

--------------------------------------------------------------------------------
-- xopEligibleFactor -

xopEligibleFactor :: ConeStruct s a -> XOrtPerspective p a
  -> Cone s p t n m a -> X (EligibleFactor s p t n m a)
xopEligibleFactor _ (XOrtProjective xos) c = xosEligibleFactorPrj xos c
xopEligibleFactor cs (XOrtInjective xos) c
  = xosEligibleFactorInj cs (dgTypeRefl $ cnDiagram c) xos c

--------------------------------------------------------------------------------
-- XStandardOrtPerspective -

class XStandardOrtPerspective p a where
  xStandardOrtPerspective :: XOrtPerspective p a

instance XStandardOrtSiteTo a => XStandardOrtPerspective Projective a where
  xStandardOrtPerspective = XOrtProjective xStandardOrtSite

instance XStandardOrtSiteFrom a => XStandardOrtPerspective Injective a where
  xStandardOrtPerspective = XOrtInjective xStandardOrtSite
