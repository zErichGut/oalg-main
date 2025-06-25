
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , TypeOperators
  , DataKinds
  , ConstraintKinds

  -- , UndecidableInstances
#-}


-- |
-- Module      : OAlg.Entity.Diagram.Diagrammatic
-- Description : objects having an underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Objects having an underlying 'Diagram'.
module OAlg.Entity.Diagram.Diagrammatic
  (

{-
    -- * Diagrammatic
    Diagrammatic(..), dgmTypeRefl

    -- * Application
  , ApplicativeDiagrammatic, FunctorialDiagrammatic

    -- * Duality
  , SDualityDiagrammatic, CoDiagrammatic(..)
  , DiagrammaticDuality(..), dgmDuality
  , DiagrammaticOpDuality, SDualityOpDiagrammatic
  , dgmOpDuality, dgmOpDualityOrt

    -- * Proposition
  , prpApplicativeDiagrammatic
  , prpCoDiagrammatic
  , prpSDualityDiagrammatic
-}
  
{-
    -- ** Duality
  , DiagrammaticOpDualisable(..)
  , DiagrammaticOpDuality(..)
  , DiagrammaticOpDuality', dgmOpDuality

    -- * Applicative
  , DiagrammaticApplicative(..), DiagrammaticApplicative1
  , DiagrammaticFunctorial, DiagrammaticFunctorial1

    -- * Proposition
  , prpDiagrammaticApplicative
  , prpDiagrammaticApplicative1
  , prpDiagrammaticOpDualisable
-}
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Either

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

import OAlg.Entity.Natural
import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m x -> Diagram t n m x

instance Diagrammatic Diagram where diagram = id

--------------------------------------------------------------------------------
-- DiagramG -

-- | wrapping a 'Diagrammatic'-object.
newtype DiagramG d (t :: DiagramType) (n :: N') (m :: N') x = DiagramG (d t n m x)
  deriving (Show,Eq)

type instance Dual1 (DiagramG d t n m) = DiagramG d (Dual t) n m

instance XStandard (d t n m x) => XStandard (DiagramG d t n m x) where
  xStandard = amap1 DiagramG xStandard

instance Oriented x => ShowDual1 (DiagramG Diagram t n m) x
instance Oriented x => EqDual1 (DiagramG Diagram t n m) x

instance (Oriented x, XStandardOrtSiteDual t x, Attestable m, n ~ m + 1)
  => XStandardDual1 (DiagramG Diagram (Chain t) n m) x

--------------------------------------------------------------------------------
-- dgmTypeRefl -

-- | the associated 'DiagramType' is bidual.
dgmTypeRefl :: Diagrammatic d => d t n m x -> Dual (Dual t) :~: t
dgmTypeRefl = dgTypeRefl . diagram

--------------------------------------------------------------------------------
-- ApplicativeDiagrammatic -

type ApplicativeDiagrammatic h d t n m
  = (Diagrammatic d, HomDisjunctiveOriented h, ApplicativeS h (DiagramG d t n m))

instance HomDisjunctiveOriented h
  => ApplicativeG (DiagramG Diagram t n m) (Variant2 Covariant h) (->) where
  amapG h (DiagramG d) = DiagramG (amapG h d)

instance ( HomDisjunctiveOriented h
         , Dual (Dual t) ~ t
         ) => ApplicativeS h (DiagramG Diagram t n m) where
  vToDual h (DiagramG d)   = DiagramG (vToDual h d)
  vFromDual h (DiagramG d) = DiagramG (vFromDual h d)

-- instance (HomDisjunctiveOriented h, Dual (Dual t) ~ t) => ApplicativeDiagrammatic h Diagram t n m

--------------------------------------------------------------------------------
-- sDiagram -

sDiagram :: Diagrammatic d => SDuality (DiagramG d t n m) x -> SDuality (Diagram t n m) x
sDiagram (SDuality sd) = SDuality $ case sd of
  Right1 (DiagramG d) -> Right1 (diagram d)
  Left1 (DiagramG d') -> Left1 (diagram d')

instance Diagrammatic d
  => Natural s (->) () (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m)) where
  roh _ _ = sDiagram
  
--------------------------------------------------------------------------------
-- NatrualDiagrammatic -

type NaturalDiagrammatic s h b d t n m
  = NaturalTransformable s h b () (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))

instance (HomDisjunctiveOriented h, Dual (Dual t) ~ t)
  => NaturalTransformable Ort h (->) () (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))

--------------------------------------------------------------------------------
-- dgmTrafo -

-- | the induced natural transformation.
dgmTrafo :: NaturalDiagrammatic s h b d t n m
    => NaturalTransformation s h b () (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
dgmTrafo = NaturalTransformation ()


ff :: ( d ~ Diagram, t ~ Chain t', t' ~ Dual (Dual t')
      , HomDisjunctiveOriented h
      , Transformable s Ort
      , TransformableG (SDuality (DiagramG d t n m)) s EqE
      , TransformableG (SDuality (Diagram t n m)) s EqE
      )
  => NaturalTransformation (SubStruct s Ort) (Sub s h) (Sub EqE (->)) ()
       (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
ff = NaturalTransformation ()

data OrtSiteX (t :: Site)

type instance Structure (OrtSiteX t) x
  = ( Oriented x
    , XStandardOrtSiteTo x
    , XStandardOrtSiteFrom x
    )

instance Transformable (OrtSiteX t) Ort where tau Struct = Struct
instance TransformableOrt (OrtSiteX t)

instance Transformable (OrtSiteX t) Typ where tau Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (DiagramG Diagram (Chain To) n m)) (OrtSiteX To) EqE where
  tauG Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (DiagramG Diagram (Chain From) n m)) (OrtSiteX From) EqE where
  tauG Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (Diagram (Chain To) n m)) (OrtSiteX To) EqE where
  tauG Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (Diagram (Chain From) n m)) (OrtSiteX From) EqE where
  tauG Struct = Struct


instance TransformableG Op (OrtSiteX t) (OrtSiteX t) where
  tauG Struct = Struct
  
instance TransformableOp (OrtSiteX t)

ggTo :: ( HomDisjunctiveOriented h
        , s ~ OrtSiteX t
        , t ~ To
        , Attestable m
        )
  => Any m
  -> NaturalTransformation (SubStruct s Ort) (Sub s h) (Sub EqE (->)) ()
       (SDuality (DiagramG Diagram (Chain t) (m+1) m)) (SDuality (Diagram (Chain t) (m+1) m))
ggTo _ = dgmTrafo

ggFrom :: ( HomDisjunctiveOriented h
          , s ~ OrtSiteX t
          , t ~ From
          , Attestable m
          )
  => Any m
  -> NaturalTransformation (SubStruct s Ort) (Sub s h) (Sub EqE (->)) ()
       (SDuality (DiagramG Diagram (Chain t) (m+1) m)) (SDuality (Diagram (Chain t) (m+1) m))
ggFrom _ = dgmTrafo

xSomeSub :: s ~ OrtSiteX t
  => Any m -> X (SomeMorphism (Sub s (HomOrtEmpty s Op)))
xSomeSub = xf where
  xoSct :: s ~ OrtSiteX t => Any m -> X (SomeObjectClass (SHom Ort s Op (HomEmpty s)))
  xoSct m = xOneOf [ SomeObjectClass (xoOS m) 
                   ]

  xoOS :: s ~ OrtSiteX t => Any m -> Struct s OS
  xoOS m = case ats m of Ats -> Struct

  xfg :: s ~ OrtSiteX t => Any m -> X (SomeCmpb2 (HomOrtEmpty s Op))
  xfg m = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomOrt f) (HomOrt g))
        $ xSctSomeCmpb2 10 (xoSct m) XEmpty

  xf :: s ~ OrtSiteX t
     => Any m
     -> X (SomeMorphism (Sub s (HomOrtEmpty s Op)))
  xf m = amap1 (\(SomeCmpb2 f g) -> SomeMorphism (sub (domain g) (range f) m (f.g))) (xfg m)

  sub :: s ~ OrtSiteX t
     => Struct s x -> Struct s y -> Any m -> HomOrtEmpty s Op x y -> Sub s (HomOrtEmpty s Op) x y
  sub Struct Struct _ = Sub


pp :: NaturalTransformation (SubStruct s Ort) (Sub s h) (Sub EqE (->)) ()
        (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))
  -> X (SomeMorphism (Sub s h))
  -> Statement
pp = prpNaturalTransformableEqExt

qqTo m = case someNatural m of
  SomeNatural m' -> pp (ggTo m') (xSomeSub m')


qqFrom m = case someNatural m of
  SomeNatural m' -> pp (ggFrom m') (xSomeSub m')
