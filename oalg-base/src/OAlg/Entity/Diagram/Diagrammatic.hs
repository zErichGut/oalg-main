
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
    Diagrammatic(..)
  , DiagramG(..), ApplicativeDiagrammaticBi
  , dgmGMap, dgmTypeRefl
  , droh, dmap

    -- * Natural
  , NaturalDiagrammatic
  , NaturalDiagrammaticDual1
  , NaturalDiagrammaticBi
  
  , NaturalDiagrammaticSDualisable, drohS
  , NaturalDiagrammaticSDualBi

    -- * Duality
  , DualisableDiagrammatic
  , DualisableDiagrammaticDual1
  , DualisableDiagrammaticBi
  , DualityDiagrammatic

  -- * Proposition
  , prpDiagrammatic

  ) where

import Control.Monad

import Data.Kind
import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify
import OAlg.Category.Path

import OAlg.Data.Either
import OAlg.Data.Constructable

import OAlg.Hom.Definition
import OAlg.Hom.Oriented

import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Additive

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

-- | wrapper for 'Diagrammatic'-objects.
newtype DiagramG d (t :: DiagramType) (n :: N') (m :: N') x = DiagramG (d t n m x)
  deriving (Show,Eq)

type instance Dual1 (DiagramG d t n m) = DiagramG d (Dual t) n m

instance Validable (d t n m x) => Validable (DiagramG d t n m x) where
  valid (DiagramG d) = valid d
  
instance XStandard (d t n m x) => XStandard (DiagramG d t n m x) where
  xStandard = amap1 DiagramG xStandard

instance Oriented x => ShowDual1 (DiagramG Diagram t n m) x
instance Oriented x => EqDual1 (DiagramG Diagram t n m) x

instance (Oriented x, XStandardOrtSite From x, Attestable m)
  => XStandardDual1 (DiagramG Diagram (Chain To) (S m) m) x
  
instance (Oriented x, XStandardOrtSite To x, Attestable m)
  => XStandardDual1 (DiagramG Diagram (Chain From) (S m) m) x

instance (Attestable m, n ~ m+1)
  => TransformableG (SDualBi (DiagramG Diagram (Chain To) n m)) OrtSiteX EqE where
  tauG Struct = Struct

instance (Attestable m, n ~ m+1)
  => TransformableG (SDualBi (DiagramG Diagram (Chain From) n m)) OrtSiteX EqE where
  tauG Struct = Struct

instance HomOriented h => ApplicativeG (DiagramG Diagram t n m) (Id2 h) (->) where
  amapG (Id2 h) (DiagramG d) = DiagramG (amapG h d)

instance TransformableOrt r => ApplicativeG (DiagramG Diagram t n m) (HomId r) (->) where
  amapG h (DiagramG d) = DiagramG (amapG h d)
  
instance TransformableOrt r => ApplicativeGDual1 (DiagramG Diagram t n m) (HomId r) (->)

instance ApplicativeG (DiagramG d t n m) (HomEmpty r) (->) where
  amapG = fromHomEmpty

instance ApplicativeGDual1 (DiagramG d t n m) (HomEmpty r) (->)

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
-- dmap -

-- | the induced mapping between the 'Diagrammatic' objects.
--
-- __Property__ Let @'ApplicativeG' ('DiagramG __d t n m) __h__ (->)@ and @h@ in @__h__@, then holds:
--
-- (1) @'DiagramG' '.' 'dmap' h '.=.' 'amapG' h '.' 'DiagramG'@.
dmap :: ApplicativeG (DiagramG d t n m) h (->)
  => h x y -> d t n m x -> d t n m y
dmap h d = d' where DiagramG d' = amapG h (DiagramG d)

--------------------------------------------------------------------------------
-- droh -

-- | the underlying diagram.
droh :: Diagrammatic d => DiagramG d t n m x -> Diagram t n m x
droh (DiagramG d) = diagram d

instance Diagrammatic d => Natural s (->) (DiagramG d t n m) (Diagram t n m) where
  roh _ = droh

--------------------------------------------------------------------------------
-- NaturalDiagrammatic -

-- | natural transformation on 'Diagrammatic' objects from @'DiagramG' __d t n m__@ to
-- @'Diagram' __t n m__@, respecting the canonical application of @__h__@ on
-- @'Diagram' __t n m__@.
--
-- __Property__ Let @'NaturalDiagrammatic' __s h d t n m__@, then for all @__x__@,
-- @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) @'amapG' h '.=.' 'dgMap' h@.
--
-- __Note__ This property is required if incoherent instances are permitted.
class
  ( Diagrammatic d
  , HomOriented h
  , NaturalTransformable h (->) (DiagramG d t n m) (Diagram t n m)
  )
  => NaturalDiagrammatic h d t n m

instance
  ( Diagrammatic d
  , TransformableOrt s
  )
  => NaturalTransformable (HomEmpty s) (->) (DiagramG d t n m) (Diagram t n m)

instance
  ( Diagrammatic d
  , TransformableOrt s
  )
  => NaturalDiagrammatic (HomEmpty s) d t n m

instance HomOriented h => NaturalTransformable (Id2 h) (->) (DiagramG Diagram t n m) (Diagram t n m)
instance HomOriented h => NaturalDiagrammatic (Id2 h) Diagram t n m
-- we need the wrapper Id2 to not get overlapped instances with the instance declaration
-- for NaturalDiagrammatic (Variant2 Covariant (HomDisj s o h)) d t n m

--------------------------------------------------------------------------------
-- prpNaturalDiagrammatic -

relNaturalDiagrammatic :: (NaturalDiagrammatic h d t n m, Show2 h)
  => q h d t n m -> Homomorphous Ort x y -> h x y -> Diagram t n m x -> Statement
relNaturalDiagrammatic _ (Struct :>: Struct) h d
  = (amapG h d == dgMap h d) :?> Params ["h":=show2 h, "d":=show d]

prpNaturalDiagrammatic :: (NaturalDiagrammatic h d t n m, Show2 h)
  => q h d t n m -> h x y -> Diagram t n m x -> Statement
prpNaturalDiagrammatic q h d = Prp "NaturalDiagrammatic"
  :<=>: relNaturalDiagrammatic q (tauHom (homomorphous h)) h d 

--------------------------------------------------------------------------------
-- NaturalDiagrammaticDual1 -

-- | helper class to avoid undecidable instances.
class NaturalDiagrammatic h d (Dual t) n m => NaturalDiagrammaticDual1 h d t n m

instance
  ( Diagrammatic d
  , TransformableOrt s
  )
  => NaturalDiagrammaticDual1 (HomEmpty s) d t n m

instance HomOriented h => NaturalDiagrammaticDual1 (Id2 h) Diagram t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticBi -

-- | constrains for diagrammatic objects @__d__@ which are bi-natural diagrammatic.
type NaturalDiagrammaticBi h d t n m =
  ( NaturalDiagrammatic h d t n m 
  , NaturalDiagrammaticDual1 h d t n m
  )

--------------------------------------------------------------------------------
-- DualisableDiagrammatic -

-- | duality for 'Diagrammatic' objects.
--
--  __Property__ Let @'DualisableDiagrammatic' __r o d t n m__@ then
-- for all @__x__@ and @r@ in @'Struct' __r x__@ holds:
--
-- For @'DualisableOriented' __r o__@ and any proxy @q@ in  @__q r o d t n m__@ holds 
--
-- (1) @'diagram' '.' 'toDualDgmLft'' q r '.=.' 'toDualGLft' r '.' 'diagram'@.
--
-- (2) @'diagram' '.' 'toDualDgmRgt'' q r '.=.' 'toDualGRgt' r '.' 'diagram'@.
class ( Diagrammatic d
      , DualisableGBi r (->) o (DiagramG d t n m)
      , TransformableGRefl o r
      , t ~ Dual (Dual t)
      )
  => DualisableDiagrammatic r o d t n m

--------------------------------------------------------------------------------
-- DiagramG - Diagram - DualisableGBi -

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         )
  => ReflexiveG s (->) o (DiagramG Diagram t n m) where
  reflG s = Inv2 (dgmGMap t) (dgmGMap f) where Inv2 t f = reflG s

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         , t' ~ Dual t, t ~ Dual t'
         )
  => DualisableGPair s (->) o (DiagramG Diagram t n m) (DiagramG Diagram t' n m) where
  toDualGLft s (DiagramG d) = DiagramG (toDualGLft s d)
  toDualGRgt s (DiagramG d) = DiagramG (toDualGRgt s d)

instance ( Transformable s Type, TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         , t ~ Dual (Dual t)
         )
  => DualisableGBi s (->) o (DiagramG Diagram t n m)

instance
  ( TransformableOrt s, TransformableType s, TransformableGRefl Op s
  , TransformableOp s
  , t ~ Dual (Dual t)
  )
  => DualisableDiagrammatic s Op Diagram t n m

--------------------------------------------------------------------------------
-- DualisableDiagrammaticDual1 -

-- | helper class to avoid undecidable instances.
class DualisableDiagrammatic s o d (Dual t) n m => DualisableDiagrammaticDual1 s o d t n m

instance
  ( TransformableOrt s, TransformableType s, TransformableGRefl Op s
  , TransformableOp s
  , t ~ Dual (Dual t)
  )
  => DualisableDiagrammaticDual1 s Op Diagram t n m

--------------------------------------------------------------------------------
-- DualisableDiagrammaticBi -

-- | constrains for dualisable diagrammatic objects @__d__@ which are bi-dual diagrammatic
-- according to @__s o__@.
type DualisableDiagrammaticBi s o d t n m =
  ( DualisableDiagrammatic s o d t n m
  , DualisableDiagrammaticDual1 s o d t n m
  )

--------------------------------------------------------------------------------
-- DualityDiagrammatic -

-- | whiteness for a 'DualisableDiagrammatic'.
data DualityDiagrammatic s o d t n m where
  DualityDiagrammatic :: DualisableDiagrammatic s o d t n m => DualityDiagrammatic s o d t n m

--------------------------------------------------------------------------------
-- toDualDgmLft -

-- | the induced mapping.
toDualDgmLft :: DualisableDiagrammatic s o d t n m
  => Struct s x -> d t n m x -> d (Dual t) n m (o x)
toDualDgmLft s d = d' where DiagramG d' = toDualGLft s (DiagramG d)

toDualDgmLft' :: DualisableDiagrammatic s o d t n m
  => q s o d t n m -> Struct s x -> d t n m x -> d (Dual t) n m (o x)
toDualDgmLft' _ = toDualDgmLft

--------------------------------------------------------------------------------
-- toDualDgmRgt -

-- | the induced mapping.
toDualDgmRgt :: DualisableDiagrammatic s o d t n m
  => Struct s x -> d (Dual t) n m x -> d t n m (o x)
toDualDgmRgt s d = d' where DiagramG d' = toDualGRgt s (DiagramG d)

toDualDgmRgt' :: DualisableDiagrammatic s o d t n m
  => q s o d t n m -> Struct s x -> d (Dual t) n m x -> d t n m (o x)
toDualDgmRgt' _ = toDualDgmRgt

--------------------------------------------------------------------------------
-- prpDualisableDiagrammatic -

relDualisableDiagrammaticLft ::
  ( DualisableOriented r o
  , TransformableOrt r
  , Show (d t n m x)
  )
  => DualityDiagrammatic r o d t n m
  -> Struct Ort (o x) -> Struct r x -> d t n m x -> Statement
relDualisableDiagrammaticLft n@DualityDiagrammatic Struct s d
  = (toDualGLft s (diagram d) == diagram (toDualDgmLft' n s d))
  :?> Params ["d":=show d]

relDualisableDiagrammaticRgt ::
  ( DualisableOriented r o
  , TransformableOrt r
  , Show (d (Dual t) n m x)
  )
  => DualityDiagrammatic r o d t n m
  -> Struct Ort (o x) -> Struct r x -> d (Dual t) n m x -> Statement
relDualisableDiagrammaticRgt n@DualityDiagrammatic Struct s d'
  = (toDualGRgt s (diagram d') == diagram (toDualDgmRgt' n s d'))
  :?> Params ["d'":=show d']

-- | validity according to 'DualisableDiagrammatic'.
prpDualisableDiagrammatic ::
  ( DualisableOriented r o
  , TransformableOrt r
  , Show (d t n m x), Show (d (Dual t) n m x)
  )
  => DualityDiagrammatic r o d t n m
  -> Struct r x -> d t n m x -> d (Dual t) n m x -> Statement
prpDualisableDiagrammatic n@DualityDiagrammatic s d d' = Prp "DualisableDiagrammatic"
  :<=>: And [ relDualisableDiagrammaticLft n (tau (tauO s)) s d
            , relDualisableDiagrammaticRgt n (tau (tauO s)) s d'
            ]

--------------------------------------------------------------------------------
-- drohS -

-- | natural assocition induced by 'droh' betewwn @'SDualBi' ('DiagramG' __d t n m__)@ and
-- @'SDualBi' ('Diagram' __t n m__)@.
drohS :: Diagrammatic d => SDualBi (DiagramG d t n m) x -> SDualBi (Diagram t n m) x
drohS (SDualBi (Right1 d)) = SDualBi (Right1 (droh d))
drohS (SDualBi (Left1 d')) = SDualBi (Left1 (droh d'))

instance Diagrammatic d
  => Natural s (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m)) where
  roh _ = drohS

--------------------------------------------------------------------------------
-- ApplicativeDiagrammaticBi -

-- | helper class to avoid undecidable instances.
class ApplicativeGBi (DiagramG d t n m) h (->) => ApplicativeDiagrammaticBi h d t n m

instance TransformableOrt r => ApplicativeDiagrammaticBi (HomId r) Diagram t n m

instance ApplicativeDiagrammaticBi (HomEmpty r) d t n m
--------------------------------------------------------------------------------
-- NaturalDiagrammaticSDualisable -

-- | natural transformation on 'Diagrammatic' objects from @'SDualBi' ('DiagramG' __d t n m__)@ to
-- @'SDualBi' ('Diagram' __t n m__)@, respecting the canonical application of @__h__@ on
-- @'SDualBi' ('Diagram' __t n m__)@.
--
-- __Property__ Let @'NaturalDiagrammaticSDualisable' __s h d t n m__@, then for all @__x__@,
-- @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) @'amapG' h '.=.' dgMapS h@.
--
-- __Note__ This property is required if incoherent instances are permitted.
class
  ( Diagrammatic d
  , HomOrientedDisjunctive h
  , NaturalTransformable h (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammaticSDualisable h d t n m

instance
  ( Morphism h
  , ApplicativeGBi (DiagramG d t n m) h (->)
  , DualisableGBi r (->) o (DiagramG d t n m)
  )
  => ApplicativeG (SDualBi (DiagramG d t n m)) (HomDisj r o h) (->) where
  amapG (HomDisj h) = amapG h

instance
  ( HomOriented h
  , TransformableOrt r
  , NaturalDiagrammaticBi h d t n m
  , ApplicativeGBi (DiagramG d t n m) h (->)
  
  , DualisableOriented r o
  , DualisableDiagrammatic r o d t n m  
  )
  => NaturalTransformable (HomDisj r o h) (->)
       (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))

instance
  ( HomOriented h
  , TransformableOrt r
  , NaturalDiagrammaticBi h d t n m
  , ApplicativeDiagrammaticBi h d t n m
  
  , DualisableOriented r o
  , DualisableDiagrammatic r o d t n m  
  )
  => NaturalDiagrammaticSDualisable (HomDisj r o h) d t n m


instance
  ( Morphism h
  , ApplicativeGBi (DiagramG d t n m) h (->)
  , DualisableGBi r (->) o (DiagramG d t n m)
  )
  => ApplicativeG (DiagramG d t n m) (Variant2 Covariant (HomDisj r o h)) (->) where
  amapG (Covariant2 h) d = d' where
    SDualBi (Right1 d') = amapG h (SDualBi (Right1 d))

instance
  ( HomOriented h
  , ApplicativeGBi (DiagramG d t n m) h (->)
  , NaturalDiagrammaticBi h d t n m
  
  , DualisableOriented r o
  , DualisableDiagrammatic r o d t n m
  )  
  => NaturalTransformable (Variant2 Covariant (HomDisj r o h)) (->) (DiagramG d t n m) (Diagram t n m)

instance
  ( HomOriented h
  , ApplicativeGBi (DiagramG d t n m) h (->)
  , NaturalDiagrammaticBi h d t n m
  
  , DualisableOriented r o
  , DualisableDiagrammatic r o d t n m
  )  
  => NaturalDiagrammatic (Variant2 Covariant (HomDisj r o h)) d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticSDualBi -

-- | whiteness of a 'NaturalDiagrammaticSDualisable'.
data NaturalDiagrammaticSDualBi h d t n m where
  NaturalDiagrammaticSDualBi :: NaturalDiagrammaticSDualisable h d t n m
    => NaturalDiagrammaticSDualBi h d t n m

--------------------------------------------------------------------------------
-- prpHomOrientedDisjunctiveS -

relHomOrientedDisjunctiveS ::
  ( HomOrientedDisjunctive h
  , ApplicativeG (SDualBi (Diagram t n m)) h (->)
  , t ~ Dual (Dual t)
  , Show2 h)
  => Homomorphous Ort x y -> h x y -> SDualBi (Diagram t n m) x -> Statement
relHomOrientedDisjunctiveS (Struct :>: Struct) h d
  = (amapG h d == dgMapS h d) :?> Params ["h":=show2 h, "d":=show d]

-- | validity of a disjunctive homomorphism on oriented structures acting
-- soundly on @'SDualit' ('Diagram' __t n m__)@ according to 'dgMapS'.
prpHomOrientedDisjunctiveS ::
  ( HomOrientedDisjunctive h
  , ApplicativeG (SDualBi (Diagram t n m)) h (->)
  , t ~ Dual (Dual t)
  , Show2 h)
  => h x y -> SDualBi (Diagram t n m) x -> Statement
prpHomOrientedDisjunctiveS h d = Prp "HomOrientedDisjunctiveS"
  :<=>: relHomOrientedDisjunctiveS (tauHom (homomorphous h)) h d

relNaturalDiagrammaticSDualisable :: (NaturalDiagrammaticSDualisable h d t n m, Show2 h)
  => q h d t n m -> h x y -> SDualBi (Diagram t n m) x -> Statement
relNaturalDiagrammaticSDualisable _ = prpHomOrientedDisjunctiveS

prpNaturalDiagrammaticSDualisable ::
  NaturalDiagrammaticSDualisable h d t n m
  => q h d t n m
  -> X (SomeNaturalApplication h (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m)))
  -> Statement
prpNaturalDiagrammaticSDualisable q xsa = Prp "NaturalDiagrammaticSDualisable"
  :<=>: Forall xsa (\(SomeNaturalApplication h d)
                    -> And [ relNaturalTransformable (n q) h d
                           , prpHomOrientedDisjunctiveS h (drohS d)
                           ]
                   )
  where n :: NaturalDiagrammaticSDualisable h d t n m
          => q h d t n m
          -> NaturalTransformation h (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))
        n _ = NaturalTransformation

--------------------------------------------------------------------------------
-- xsoOrtSite -

-- | random variable for some object classees of @'SHom' __s s 'Op' __h__@.
xsoOrtSite :: s ~ OrtSiteX => X (SomeObjectClass (SHom s s Op h))
xsoOrtSite = xOneOf [ SomeObjectClass (Struct :: Struct OrtSiteX OS)
                    , SomeObjectClass (Struct :: Struct OrtSiteX (Op OS))
                    , SomeObjectClass (Struct :: Struct OrtSiteX (U N))
                    ]

--------------------------------------------------------------------------------
-- HomTest -

-- | type for test homs.
type HomTest s = HomDisj s Op (HomId s)

--------------------------------------------------------------------------------
-- xsOrtSiteXOp -

-- | random variable for some object classees of @'HomTest' __s__@.
xsOrtSiteXOp :: X (SomeMorphism (HomTest OrtSiteX))
xsOrtSiteXOp = amap1 smCmpb2 $ xscmHomDisj xsoOrtSite xhid where
  xhid = xOneOf [ SomeMorphism (ToId   :: HomId OrtSiteX OS (Id OS))
                , SomeMorphism (FromId :: HomId OrtSiteX (Id OS) OS)
                , SomeMorphism (ToId   :: HomId OrtSiteX (U N) (Id (U N)))
                , SomeMorphism (FromId :: HomId OrtSiteX (Id (U Z)) (U Z)) 
                ]
         
--------------------------------------------------------------------------------
-- xsaChainTo -

xdChainToStruct :: (n ~ m+1, t ~ Chain To, Show2 h)
  => Any m
  -> Homomorphous OrtSiteX x y 
  -> h x y
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdChainToStruct m (Struct :>: Struct) h = do
  b <- xBool
  case b of
    True  -> do
      d <- xDiagram Refl (XDiagramChainTo m xStandardOrtSite)
      return (SomeNaturalApplication h (SDualBi (Right1 (DiagramG d))))
    False -> do
      d <- xDiagram Refl (XDiagramChainFrom m xStandardOrtSite)
      return (SomeNaturalApplication h (SDualBi (Left1 (DiagramG d))))

xdChainTo ::
  ( Morphism h
  , ObjectClass h ~ OrtSiteX
  , n ~ m+1, t ~ Chain To, Show2 h
  )
  => Any m
  -> h x y
  -> X (SomeNaturalApplication h
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdChainTo m h = xdChainToStruct m (homomorphous h) h


xsaChainTo ::(n ~ m+1, t ~ Chain To)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaChainTo m = do
  SomeMorphism h <- xsOrtSiteXOp
  xdChainTo m h


--------------------------------------------------------------------------------
-- xsaSink -

xdSinkStruct :: (n ~ m+1, t ~ Star To, Show2 h)
  => Any m
  -> Homomorphous OrtSiteX x y 
  -> h x y
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdSinkStruct m (Struct :>: Struct) h = do
  b <- xBool
  case b of
    True  -> do
      d <- xDiagram Refl (XDiagramSink m xStandardOrtSite)
      return (SomeNaturalApplication h (SDualBi (Right1 (DiagramG d))))
    False -> do
      d <- xDiagram Refl (XDiagramSource m xStandardOrtSite)
      return (SomeNaturalApplication h (SDualBi (Left1 (DiagramG d))))

xdSink ::
  ( Morphism h
  , ObjectClass h ~ OrtSiteX
  , n ~ m+1, t ~ Star To, Show2 h
  )
  => Any m
  -> h x y
  -> X (SomeNaturalApplication h
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdSink m h = xdSinkStruct m (homomorphous h) h

xsaSink ::(n ~ m+1, t ~ Star To)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaSink m = do
  SomeMorphism h <- xsOrtSiteXOp
  xdSink m h

--------------------------------------------------------------------------------
-- snaDual -

instance TransformableOrt s
  => NaturalTransformable (HomId s) (->) (DiagramG Diagram t n m) (Diagram t n m)

instance TransformableOrt s => NaturalDiagrammatic (HomId s) Diagram t n m
instance TransformableOrt s => NaturalDiagrammaticDual1 (HomId s) Diagram t n m

isoHomTest :: TransformableGRefl Op s => HomTest s x y
  -> Variant2 Contravariant (IsoHomDisj s Op (HomId s)) x (Op x) 
isoHomTest = isoHomDisj . domain

snaDual ::
  ( TransformableOrt s
  , TransformableType s
  , TransformableOp s
  , TransformableGRefl Op s
  , t ~ Dual (Dual t)
  )
  => SomeNaturalApplication (HomTest s)
        (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m))    
  -> SomeNaturalApplication (HomTest s)
        (SDualBi (DiagramG Diagram (Dual t) n m)) (SDualBi (Diagram (Dual t) n m))
snaDual (SomeNaturalApplication h sd) = case (tauOrt (domain h), tauOrt (range h)) of
    (Struct,Struct) -> SomeNaturalApplication (h . f) sd' where

      Contravariant2 (Inv2 t f) = isoHomTest h

      sd' = case amapG t sd of
        SDualBi (Right1 d) -> SDualBi (Left1 d)
        SDualBi (Left1 d') -> SDualBi (Right1 d') 

--------------------------------------------------------------------------------
-- xsaChainFrom -

xsaChainFrom :: (n ~ m+1, t ~ Chain From)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaChainFrom m = amap1 snaDual $ xsaChainTo m

--------------------------------------------------------------------------------
-- xsaSource -

xsaSource ::(n ~ m+1, t ~ Star From)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaSource m = amap1 snaDual $ xsaSink m

--------------------------------------------------------------------------------
-- OrtOrientationX -

data OrtOrientationX

type instance Structure OrtOrientationX x = (Oriented x, XStandardOrtOrientation x)

instance Transformable OrtOrientationX Typ where tau Struct = Struct

instance Transformable OrtOrientationX Ort where tau Struct = Struct
instance TransformableOrt OrtOrientationX

instance TransformableG Op OrtOrientationX OrtOrientationX where tauG Struct = Struct
instance TransformableGRefl Op OrtOrientationX
instance TransformableOp OrtOrientationX

instance Transformable OrtOrientationX Type where tau Struct = Struct
instance TransformableType OrtOrientationX

--------------------------------------------------------------------------------
-- xsoOrtOrientation -

xsoOrtOrientation :: s ~ OrtOrientationX => X (SomeObjectClass (SHom s s Op h))
xsoOrtOrientation
  = xOneOf [ SomeObjectClass (Struct :: Struct OrtOrientationX OS)
           , SomeObjectClass (Struct :: Struct OrtOrientationX (Op OS))
           , SomeObjectClass (Struct :: Struct OrtOrientationX (U Z))
           ]


xsOrtOrientationXOp ::  s ~ OrtOrientationX => X (SomeMorphism (HomTest s))
xsOrtOrientationXOp = amap1 smCmpb2 $ xscmHomDisj xsoOrtOrientation xhid where
  xhid = xOneOf [ SomeMorphism (ToId   :: HomId OrtOrientationX OS (Id OS))
                , SomeMorphism (FromId :: HomId OrtOrientationX (Id OS) OS)
                , SomeMorphism (ToId   :: HomId OrtOrientationX  (U N) (Id (U N)))
                , SomeMorphism (FromId :: HomId OrtOrientationX  (Id (U Z)) (U Z)) 
                ]


dstOrtOrientationXOp :: Int -> IO ()
dstOrtOrientationXOp n = putDstr asp n xsOrtOrientationXOp where
  asp h = [show (ind a, ind b, ind c)] where (a,b,c) = sta h

  ind :: N -> N
  ind 0 = 0
  ind _ = 1

  sta :: SomeMorphism (HomTest s) -> (N,N,N)
  sta (SomeMorphism (HomDisj h)) = staPath (form h) (0,0,0)

  staPath :: Path (SMorphism r s o h) x y -> (N,N,N) -> (N,N,N)
  staPath (IdPath _) res   = res
  staPath (h :. p) (c,t,f) = staPath p res' where
    res' = case h of
      SCov _    -> (c+1,t,f)
      SToDual   -> (c,t+1,f)
      SFromDual -> (c,t,f+1)
  
--------------------------------------------------------------------------------
-- xsaParallelLR -

xdParallelLRStruct :: (n ~ N2, t ~ Parallel LeftToRight, Show2 h)
  => Any m
  -> Homomorphous OrtOrientationX x y 
  -> h x y
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdParallelLRStruct m (Struct :>: Struct) h = do
  b <- xBool
  case b of
    True  -> do
      d <- xDiagram Refl (XDiagramParallelLR m xStandardOrtOrientation)
      return (SomeNaturalApplication h (SDualBi (Right1 (DiagramG d))))
    False -> do
      d <- xDiagram Refl (XDiagramParallelRL m xStandardOrtOrientation)
      return (SomeNaturalApplication h (SDualBi (Left1 (DiagramG d))))

xdParallelLR ::
  ( Morphism h, Show2 h
  , ObjectClass h ~ OrtOrientationX
  , n ~ N2, t ~ Parallel LeftToRight
  )
  => Any m
  -> h x y
  -> X (SomeNaturalApplication h
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdParallelLR m h = xdParallelLRStruct m (homomorphous h) h

xsaParallelLR ::(n ~ N2, t ~ Parallel LeftToRight)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtOrientationX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaParallelLR m = do
  SomeMorphism h <- xsOrtOrientationXOp
  xdParallelLR m h

--------------------------------------------------------------------------------
-- xsaParallelRL -

xsaParallelRL ::(n ~ N2, t ~ Parallel RightToLeft)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtOrientationX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaParallelRL m = amap1 snaDual $ xsaParallelLR m

--------------------------------------------------------------------------------
-- prpDiagrammtic -

-- | validity according to 'NaturalDiagrmmaticS' for some @'HomDisjEmpty' 'OrtSiteX' 'Op'@
-- acting on some 'Diagram's.
prpDiagrammatic :: N -> Statement
prpDiagrammatic nMax = Prp "Diagrammatic"
  :<=>: And [ Forall (xNB 0 nMax)
                (\m -> case someNatural m of
                  SomeNatural m' -> And [ prpNaturalDiagrammaticSDualisable (chT m') (xsaChainTo m')
                                        , prpNaturalDiagrammaticSDualisable (chF m') (xsaChainFrom m')
                                        , prpNaturalDiagrammaticSDualisable (skT m') (xsaSink m')
                                        , prpNaturalDiagrammaticSDualisable (skF m') (xsaSource m')
                                        , prpNaturalDiagrammaticSDualisable (lrT m') (xsaParallelLR m')
                                        , prpNaturalDiagrammaticSDualisable (lrF m') (xsaParallelRL m')
                                        ]
                )
            ]
  where chT :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram (Chain To) (m+1) m
        chT _ = NaturalDiagrammaticSDualBi

        chF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram (Chain From) (m+1) m
        chF _ = NaturalDiagrammaticSDualBi

        skT :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram (Star To) (m+1) m
        skT _ = NaturalDiagrammaticSDualBi

        skF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram (Star From) (m+1) m
        skF _ = NaturalDiagrammaticSDualBi

        lrT :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram
               (Parallel LeftToRight) N2 m
        lrT _ = NaturalDiagrammaticSDualBi

        lrF :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticSDualBi (HomTest s) Diagram
               (Parallel RightToLeft) N2 m
        lrF _ = NaturalDiagrammaticSDualBi


