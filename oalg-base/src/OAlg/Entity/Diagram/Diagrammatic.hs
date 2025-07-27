
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
#-}

-- |
-- Module      : OAlg.Entity.Diagram.Diagrammatic
-- Description : objects with a naturally underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Objects with a naturally underlying 'Diagram'.
module OAlg.Entity.Diagram.Diagrammatic
  (
    -- * Diagrammatic
    Diagrammatic(..), DiagramG(..), dgmGMap, dgmTypeRefl

    -- * Applicative
  , ApplicativeDiagrammatic
  , NaturalDiagrammaticS

    -- * Natural
  , rohDiagram

    -- * Proposition
  , prpNaturalDiagrammaticTrafoChain
  ) where

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Either

import OAlg.Hom.Definition
import OAlg.Hom.Oriented

import OAlg.Structure.Oriented

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

instance (Oriented x, XStandardOrtSite From x, Attestable m)
  => XStandardDual1 (DiagramG Diagram (Chain To) (S m) m) x
  
instance (Oriented x, XStandardOrtSite To x, Attestable m)
  => XStandardDual1 (DiagramG Diagram (Chain From) (S m) m) x

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (DiagramG Diagram (Chain To) n m)) OrtSiteX EqE where
  tauG Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDuality (DiagramG Diagram (Chain From) n m)) OrtSiteX EqE where
  tauG Struct = Struct

--------------------------------------------------------------------------------
-- dgmGMap -

-- | the induced mapping.
dgmGMap :: (d t n m x -> d t n m y) -> DiagramG d t n m x -> DiagramG d t n m y
dgmGMap f (DiagramG d) = DiagramG (f d)

--------------------------------------------------------------------------------
-- dgmTypeRefl -

-- | the associated 'DiagramType' is bidual.
dgmTypeRefl :: Diagrammatic d => d t n m x -> Dual (Dual t) :~: t
dgmTypeRefl = dgTypeRefl . diagram

--------------------------------------------------------------------------------
-- ApplicativeDiagrammatic -

-- | applications on 'Diagrammatic' objects.
class ( Morphism h
      , ApplicativeG (DiagramG d t n m) h (->)
      , ApplicativeG (DiagramG d (Dual t) n m) h (->)
      )
  => ApplicativeDiagrammatic h d t n m

instance HomOriented h => ApplicativeG (DiagramG Diagram t n m) h (->) where
  amapG h (DiagramG d) = DiagramG (amapG h d)
  
instance HomOriented h => ApplicativeDiagrammatic h Diagram t n m

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         )
  => ReflexiveG s (->) o (DiagramG Diagram t n m) where
  reflG s = Inv2 (dgmGMap t) (dgmGMap f) where Inv2 t f = reflG s

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         , t' ~ Dual t, t ~ Dual t'
         )
  => DualisableGBi s (->) o (DiagramG Diagram t n m) (DiagramG Diagram t' n m) where
  toDualGLft s (DiagramG d) = DiagramG (toDualGLft s d)
  toDualGRgt s (DiagramG d) = DiagramG (toDualGRgt s d)

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         , t ~ Dual (Dual t)
         )
  => DualisableGBiDual1 s (->) o (DiagramG Diagram t n m)

{-
instance ( ApplicativeDiagrammatic h d t n m
         , DualisableGBiDual1 s (->) o (DiagramG d t n m)
         )
-}
instance NaturalDiagrammaticS s o h d t n m
  => ApplicativeG (SDuality (DiagramG d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smap h

--------------------------------------------------------------------------------
-- rohDiagram -

-- | the canonical transformation,
rohDiagram :: Diagrammatic d => SDuality (DiagramG d t n m) x -> SDuality (Diagram t n m) x
rohDiagram (SDuality sd) = SDuality $ case sd of
  Right1 (DiagramG d) -> Right1 (diagram d)
  Left1 (DiagramG d') -> Left1 (diagram d')

instance Diagrammatic d
  => Natural s (->) (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m)) where
  roh _ = rohDiagram


class ( Diagrammatic d
      , ApplicativeDiagrammatic h d t n m
      , DualisableGBiDual1 s (->) o (DiagramG d t n m)
      , t ~ Dual (Dual t)
      , TransformableGRefl o s, TransformableOrt s
      )
  => NaturalDiagrammaticS s o h d t n m


instance ( HomOriented h, DualisableOriented s o
         , NaturalDiagrammaticS s o h d t n m
         )
  => NaturalTransformable s (HomDisj s o h) (->)
      (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))

instance t ~ Dual (Dual t) => NaturalDiagrammaticS OrtSiteX Op (HomEmpty OrtSiteX) Diagram t n m



{-
--------------------------------------------------------------------------------
-- NaturalDiagrammatic -

-- | diagrammatic objects admitting a natural transformability.
class ( Diagrammatic d
      , NaturalTransformable s (HomDisj s o h) (->)
        (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
      ) => NaturalDiagrammatic s o h d t n m

instance ( HomOriented h
         , TransformableOrt s, Transformable s Type, TransformableGRefl o s
         , DualisableOriented s o, t ~ Dual (Dual t)
         )
  => NaturalDiagrammatic s o h Diagram t n m
-}
--------------------------------------------------------------------------------
-- prpNaturalDiagrammaticTrafoChain -

dgmtDiagram :: ( t ~ Dual (Dual t)
               , TransformableG (SDuality (DiagramG Diagram t n m)) s EqE
               , TransformableG (SDuality (Diagram t n m)) s EqE
               , s ~ OrtSiteX
               )
  => NaturalTransformation (SubStruct s s) (Sub s (HomDisjEmpty s Op)) (Sub EqE (->))
       (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))
dgmtDiagram = NaturalTransformation

dgmtDiagramChainTo :: (s ~ OrtSiteX, t ~ Chain To, n ~ m + 1, Attestable m)
  => q m
  -> NaturalTransformation (SubStruct s s) (Sub s (HomDisjEmpty s Op)) (Sub EqE (->))
       (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))
dgmtDiagramChainTo _ = dgmtDiagram

dgmtDiagramChainFrom :: (s ~ OrtSiteX, t ~ Chain From, n ~ m + 1, Attestable m)
  => q m
  -> NaturalTransformation (SubStruct s s) (Sub s (HomDisjEmpty s Op)) (Sub EqE (->))
       (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))
dgmtDiagramChainFrom _ = dgmtDiagram


xsoOrt :: s ~ OrtSiteX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoOrt = xOneOf [ SomeObjectClass (Struct :: Struct OrtSiteX OS)
                 , SomeObjectClass (Struct :: Struct OrtSiteX (Op OS))
                 , SomeObjectClass (Struct :: Struct OrtSiteX (U N))
                 ]


-- | random variable for some @'Sub' 'OrtSiteX'@ on @'HomDisjEmpty' 'OrtSiteX' 'Op')@
xsOrtSiteXOp :: s ~ OrtSiteX => X (SomeMorphism (Sub s (HomDisjEmpty s Op)))
xsOrtSiteXOp = amap1 (sub . smCmpb2) $ xscmHomDisj xsoOrt XEmpty where
  subStruct :: Homomorphous s x y -> h x y -> Sub s h x y
  subStruct (Struct :>: Struct) = Sub
  
  sub :: s ~ OrtSiteX => SomeMorphism (HomDisjEmpty s Op) -> SomeMorphism (Sub s (HomDisjEmpty s Op))
  sub (SomeMorphism h) = SomeMorphism (subStruct (homomorphous h) h)


-- | validity of
-- @'NaturalDiagrammaticTrafo' 'Ort' ('HomDisjEmpty' 'Ort' 'Op') (->)
-- 'Diagram' ('Chain' __t__) __m+1__ __m__@.
prpNaturalDiagrammaticTrafoChain :: Statement
prpNaturalDiagrammaticTrafoChain = Prp "NaturalDiagrammaticTrafoChain"
  :<=>: Forall (xTupple2 xBool (xNB 0 10)) (uncurry rel)
  
  where
    rel b m           = case someNatural m of
      SomeNatural m' -> case b of
        True  -> prpNaturalTransformableEqExt (dgmtDiagramChainTo m') xsOrtSiteXOp
        False -> prpNaturalTransformableEqExt (dgmtDiagramChainFrom m') xsOrtSiteXOp


