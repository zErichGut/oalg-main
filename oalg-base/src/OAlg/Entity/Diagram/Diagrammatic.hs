
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
  ( -- * Diagrammatic
    Diagrammatic(..), DiagramG(..), dgmTypeRefl
  , sDiagram

    -- * Applicative
  , ApplicativeDiagrammatic

    -- * Natural Transformation
  , NaturalDiagrammatic, NaturalDiagrammaticTrafo, dgmTrafo

    -- * Proposition
  , prpNaturalDiagrammaticTrafoChain
    
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Either

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

--------------------------------------------------------------------------------
-- sDiagram -

-- | the canonical transformation,
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
  = ( Diagrammatic d
    , NaturalTransformable s h b () (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
    )

instance (HomDisjunctiveOriented h, Dual (Dual t) ~ t)
  => NaturalTransformable Ort h (->) () (SDuality (DiagramG Diagram t n m)) (SDuality (Diagram t n m))

--------------------------------------------------------------------------------
-- NatrualDiagrammaticTrafo -

-- | witness of a 'NaturalDiagrammatic'.
type NaturalDiagrammaticTrafo s h b d t n m
  = NaturalTransformation s h b () (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
  
--------------------------------------------------------------------------------
-- dgmTrafo -

-- | the induced natural transformation.
dgmTrafo :: NaturalDiagrammatic s h b d t n m => NaturalDiagrammaticTrafo s h b d t n m
dgmTrafo = NaturalTransformation ()

--------------------------------------------------------------------------------
-- prpNaturalDiagrammaticTrafoChain -

-- | 'NaturalDiagrammaticTrafo' to @'Sub' 'EqE' (->)@ for @'Diagram' ('Chain' 'To')@.
dgmtDiagramChainTo :: (HomDisjunctiveOriented h, s ~ OrtSiteX, Attestable m)
  => q m
  -> NaturalDiagrammaticTrafo (SubStruct s Ort) (Sub s h) (Sub EqE (->)) Diagram (Chain To) (m+1) m
dgmtDiagramChainTo _ = dgmTrafo

-- | 'NaturalDiagrammaticTrafo' to @'Sub' 'EqE' (->)@ for @'Diagram' ('Chain' 'From')@.
dgmtDiagramChainFrom :: (HomDisjunctiveOriented h, s ~ OrtSiteX, Attestable m)
  => q m
  -> NaturalDiagrammaticTrafo (SubStruct s Ort) (Sub s h) (Sub EqE (->)) Diagram (Chain From) (m+1) m
dgmtDiagramChainFrom _ = dgmTrafo

-- | random variable for some @'Sub' 'OrtSiteX'@ on @'HomDisjEmpty' 'OrtSiteX' 'Op')@
xsOrtSiteXOp :: s ~ OrtSiteX
  => X (SomeMorphism (Sub s (HomDisjEmpty s Op)))
xsOrtSiteXOp = xf where
  xoSct :: s ~ OrtSiteX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
  xoSct = xOneOf [ SomeObjectClass (Struct :: Struct OrtSiteX OS)
                 , SomeObjectClass (Struct :: Struct OrtSiteX (Op OS))
                 , SomeObjectClass (Struct :: Struct OrtSiteX (U N))
                 ]

  xfg :: s ~ OrtSiteX => X (SomeCmpb2 (HomDisjEmpty s Op))
  xfg = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomDisj f) (HomDisj g))
      $ xSctSomeCmpb2 10 xoSct XEmpty

  xf :: s ~ OrtSiteX
     => X (SomeMorphism (Sub s (HomDisjEmpty s Op)))
  xf = amap1 (\(SomeCmpb2 f g) -> SomeMorphism (sub (domain g) (range f) (f.g))) xfg

  sub :: s ~ OrtSiteX
     => Struct s x -> Struct s y -> HomDisjEmpty s Op x y -> Sub s (HomDisjEmpty s Op) x y
  sub Struct Struct = Sub


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

