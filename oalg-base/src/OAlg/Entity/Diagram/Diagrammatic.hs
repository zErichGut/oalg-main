
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
  , droh, dmap

    -- * Natural
  , NaturalDiagrammatic, NaturalDiagrammaticDual1
  , NaturalDiagrammaticSDualisable, drohS
  , NaturalDiagrammaticSDualBi

  , NaturalDiagrammaticObjectClass, NaturalDiagrammaticObjectClassDual1
  
    -- * Duality
  , DualisableDiagrammatic, DualisableDiagrammaticDual1
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
dmap :: ApplicativeG (DiagramG d t n m) h (->)
  => h x y -> d t n m x -> d t n m y
dmap h d = d' where DiagramG d' = amapG h (DiagramG d)

--------------------------------------------------------------------------------
-- DiagramG - Diagram - DualisableGBiDual1 -

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

--------------------------------------------------------------------------------
-- DualisableDiagrammatic -

-- | duality for 'Diagrammatic' objects.
--
--  __Property__ Let @'DualisableDiagrammatic' __s o d t n m__@ then
-- for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'diagram' '.' 'toDualLftDgm'' n s '.=.' 'toDualGLft' s '.' 'diagram'@.
--
-- (2) @'diagram' '.' 'toDualRgtDgm'' n s '.=.' 'toDualGRgt' s '.' 'diagram'@.
--
-- where @n@ is a proxy in  @__q s o d t n m__@.
class ( Diagrammatic d
      , DualisableGBiDual1 s (->) o (DiagramG d t n m)
      , DualisableOriented s o, TransformableOrt s, TransformableGRefl o s
      , t ~ Dual (Dual t)
      )
  => DualisableDiagrammatic s o d t n m

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
-- DualityDiagrammatic -

-- | whiteness for a 'DualisableDiagrammatic'.
data DualityDiagrammatic s o d t n m where
  DualityDiagrammatic :: DualisableDiagrammatic s o d t n m => DualityDiagrammatic s o d t n m

--------------------------------------------------------------------------------
-- toDualLftDgm -

-- | the induced mapping.
toDualLftDgm :: DualisableDiagrammatic s o d t n m
  => Struct s x -> d t n m x -> d (Dual t) n m (o x)
toDualLftDgm s d = d' where DiagramG d' = toDualGLft s (DiagramG d)

toDualLftDgm' :: DualisableDiagrammatic s o d t n m
  => q s o d t n m -> Struct s x -> d t n m x -> d (Dual t) n m (o x)
toDualLftDgm' _ = toDualLftDgm

--------------------------------------------------------------------------------
-- toDualRgtDgm -

-- | the induced mapping.
toDualRgtDgm :: DualisableDiagrammatic s o d t n m
  => Struct s x -> d (Dual t) n m x -> d t n m (o x)
toDualRgtDgm s d = d' where DiagramG d' = toDualGRgt s (DiagramG d)

toDualRgtDgm' :: DualisableDiagrammatic s o d t n m
  => q s o d t n m -> Struct s x -> d (Dual t) n m x -> d t n m (o x)
toDualRgtDgm' _ = toDualRgtDgm

--------------------------------------------------------------------------------
-- prpDualisableDiagrammatic -

relDualisableDiagrammaticLft :: Show (d t n m x)
  => DualityDiagrammatic s o d t n m
  -> Struct Ort (o x) -> Struct s x -> d t n m x -> Statement
relDualisableDiagrammaticLft n@DualityDiagrammatic Struct s d
  = (toDualGLft s (diagram d) == diagram (toDualLftDgm' n s d))
  :?> Params ["d":=show d]

relDualisableDiagrammaticRgt :: (Show (d (Dual t) n m x))
  => DualityDiagrammatic s o d t n m
  -> Struct Ort (o x) -> Struct s x -> d (Dual t) n m x -> Statement
relDualisableDiagrammaticRgt n@DualityDiagrammatic Struct s d'
  = (toDualGRgt s (diagram d') == diagram (toDualRgtDgm' n s d'))
  :?> Params ["d'":=show d']

-- | validity according to 'DualisableDiagrammatic'.
prpDualisableDiagrammatic :: (Show (d t n m x), Show (d (Dual t) n m x))
  => DualityDiagrammatic s o d t n m
  -> Struct s x -> d t n m x -> d (Dual t) n m x -> Statement
prpDualisableDiagrammatic n@DualityDiagrammatic s d d' = Prp "DualisableDiagrammatic"
  :<=>: And [ relDualisableDiagrammaticLft n (tau (tauO s)) s d
            , relDualisableDiagrammaticRgt n (tau (tauO s)) s d'
            ]

--------------------------------------------------------------------------------
-- droh -

-- | the underlying diagram.
droh :: Diagrammatic d => DiagramG d t n m x -> Diagram t n m x
droh (DiagramG d) = diagram d

instance Diagrammatic d => Natural s (->) (DiagramG d t n m) (Diagram t n m) where
  roh _ = droh

--------------------------------------------------------------------------------
-- TransformableHom -

-- | helper class to avoid undecidable instances.
class Transformable (ObjectClass h) s => TransformableHom h s

instance Transformable r s => TransformableHom (HomId r) s

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
class (HomOriented h, NaturalTransformable s h (->) (DiagramG d t n m) (Diagram t n m))
  => NaturalDiagrammatic s h d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammatic - Diagram - 

instance (HomOriented h, TransformableHom h s)
  => NaturalTransformable s (Id2 h) (->) (DiagramG Diagram t n m) (Diagram t n m)

instance (HomOriented h, TransformableHom h s)
  => NaturalDiagrammatic s (Id2 h) Diagram t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammatic - HomEmpty - 

instance ApplicativeG (DiagramG d t n m) (HomEmpty s) c where amapG = fromHomEmpty

instance (Diagrammatic d, TransformableOrt s, Transformable s r)
  => NaturalTransformable r (HomEmpty s) (->) (DiagramG d t n m) (Diagram t n m)

instance (Diagrammatic d, TransformableOrt s, Transformable s r)
  => NaturalDiagrammatic r (HomEmpty s) d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammatic - HomDisjEmpty - 

instance DualisableDiagrammatic s o d t n m
  => ApplicativeG (DiagramG d t n m) (Variant2 Covariant (HomDisjEmpty s o)) (->) where
  amapG (Covariant2 (HomDisj h)) d = d' where
    SDualBi (Right1 d') = smapBi h (SDualBi (Right1 d))

instance (DualisableDiagrammatic s o d t n m, Transformable s r)
  => NaturalTransformable r (Variant2 Covariant (HomDisjEmpty s o)) (->)
         (DiagramG d t n m) (Diagram t n m)
         
instance (DualisableDiagrammatic s o d t n m, Transformable s r)
  => NaturalDiagrammatic r (Variant2 Covariant (HomDisjEmpty s o)) d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticDual1 -

-- | helper class to avoid undecidable instances.
class NaturalDiagrammatic s h d (Dual t) n m => NaturalDiagrammaticDual1 s h d t n m

instance (HomOriented h, TransformableHom h s)
  => NaturalDiagrammaticDual1 s (Id2 h) Diagram t n m

instance (Diagrammatic d, TransformableOrt s, Transformable s r)
  => NaturalDiagrammaticDual1 r (HomEmpty s) d t n m

--------------------------------------------------------------------------------
-- prpNaturalDiagrammatic -

relNaturalDiagrammatic :: (NaturalDiagrammatic s h d t n m, Show2 h)
  => q s h d t n m -> Homomorphous Ort x y -> h x y -> Diagram t n m x -> Statement
relNaturalDiagrammatic _ (Struct :>: Struct) h d
  = (amapG h d == dgMap h d) :?> Params ["h":=show2 h, "d":=show d]

prpNaturalDiagrammatic :: (NaturalDiagrammatic s h d t n m, Show2 h)
  => q s h d t n m -> h x y -> Diagram t n m x -> Statement
prpNaturalDiagrammatic q h d = Prp "NaturalDiagrammatic"
  :<=>: relNaturalDiagrammatic q (tauHom (homomorphous h)) h d 

--------------------------------------------------------------------------------
-- NaturalDiagrammaticObjectClass -

-- | helper class to avoid undecidable instances.
class NaturalDiagrammatic (ObjectClass h) h d t n m
  => NaturalDiagrammaticObjectClass h d t n m

instance (Diagrammatic d, TransformableOrt s)
  => NaturalDiagrammaticObjectClass (HomEmpty s) d t n m

instance
  ( DualisableDiagrammatic s o d t n m
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammaticObjectClass (Variant2 Covariant (HomDisjEmpty s o)) d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticObjectClassDual1 -

-- | helper class to avoid undecidable instances.
class NaturalDiagrammaticObjectClass h d (Dual t) n m
  => NaturalDiagrammaticObjectClassDual1 h d t n m

instance (Diagrammatic d, TransformableOrt s)
  => NaturalDiagrammaticObjectClassDual1 (HomEmpty s) d t n m

--------------------------------------------------------------------------------
-- drohS -

-- | natural assocition betewwn @'SDualBi' ('DiagramG' __d t n m)@ and
-- @'SDualBi' ('Diagram' t n m)@
drohS :: Diagrammatic d => SDualBi (DiagramG d t n m) x -> SDualBi (Diagram t n m) x
drohS (SDualBi (Right1 d)) = SDualBi (Right1 (droh d))
drohS (SDualBi (Left1 d')) = SDualBi (Left1 (droh d'))


instance Diagrammatic d
  => Natural s (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m)) where
  roh _ = drohS

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
  , NaturalTransformable s h (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammaticSDualisable s h d t n m

instance
  ( NaturalDiagrammatic s h d t n m
  , NaturalDiagrammaticDual1 s h d t n m
  , DualisableDiagrammatic s o d t n m
  )
  => ApplicativeG (SDualBi (DiagramG d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smapBi h

instance
  ( NaturalDiagrammatic s h d t n m
  , NaturalDiagrammaticDual1 s h d t n m
  , DualisableDiagrammatic s o d t n m
  , Transformable s r
  )
  => NaturalTransformable r (HomDisj s o h) (->)
       (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))

instance
  ( NaturalDiagrammatic s h d t n m
  , NaturalDiagrammaticDual1 s h d t n m
  , DualisableDiagrammatic s o d t n m
  , Transformable s r
  )
  => NaturalDiagrammaticSDualisable r (HomDisj s o h) d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticSDualBi -

-- | whiteness of a 'NaturalDiagrammaticSDualisable'.
data NaturalDiagrammaticSDualBi s h d t n m where
  NaturalDiagrammaticSDualBi :: NaturalDiagrammaticSDualisable s h d t n m
    => NaturalDiagrammaticSDualBi s h d t n m

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

relNaturalDiagrammaticSDualisable :: (NaturalDiagrammaticSDualisable s h d t n m, Show2 h)
  => q s h d t n m -> h x y -> SDualBi (Diagram t n m) x -> Statement
relNaturalDiagrammaticSDualisable _ = prpHomOrientedDisjunctiveS

prpNaturalDiagrammaticSDualisable ::
  NaturalDiagrammaticSDualisable s h d t n m
  => q s h d t n m
  -> X (SomeNaturalApplication h (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m)))
  -> Statement
prpNaturalDiagrammaticSDualisable q xsa = Prp "NaturalDiagrammaticSDualisable"
  :<=>: Forall xsa (\(SomeNaturalApplication h d)
                    -> And [ prpHomOrientedDisjunctiveS h (drohS d)
                           , relNaturalTransformable (n q) h d
                           ]
                   )
  where n :: NaturalDiagrammaticSDualisable s h d t n m
          => q s h d t n m
          -> NaturalTransformation s h (->) (SDualBi (DiagramG d t n m)) (SDualBi (Diagram t n m))
        n _ = NaturalTransformation
  
--------------------------------------------------------------------------------
-- xsoOrtSite -

-- | random variable for some object classees of @'SHom' __s s__ ('HomEmpty' __s__)@.
xsoOrtSite :: (s ~ OrtSiteX)
  => X (SomeObjectClass (SHom s s Op h))
xsoOrtSite = xOneOf [ SomeObjectClass (Struct :: Struct OrtSiteX OS)
                    , SomeObjectClass (Struct :: Struct OrtSiteX (Op OS))
                    , SomeObjectClass (Struct :: Struct OrtSiteX (U N))
                    ]


-- | random variable for some @'Sub' 'OrtSiteX'@ on @'HomDisjEmpty' 'OrtSiteX' 'Op')@
xsOrtSiteXOp :: (s ~ OrtSiteX, h ~ HomEmpty s)
  => X (SomeMorphism (HomDisj s Op h))
xsOrtSiteXOp = amap1 smCmpb2 $ xscmHomDisj xsoOrtSite XEmpty

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
  , s ~ OrtSiteX, n ~ m+1, t ~ Chain To, Show2 h
  )
  => Any m
  -> HomDisj s Op h x y
  -> X (SomeNaturalApplication (HomDisj s Op h)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdChainTo m h = xdChainToStruct m (homomorphous h) h


xsaChainTo ::
  ( s ~ OrtSiteX, n ~ m+1, t ~ Chain To
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisjEmpty s Op)
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
  , s ~ OrtSiteX, n ~ m+1, t ~ Star To, Show2 h
  )
  => Any m
  -> HomDisj s Op h x y
  -> X (SomeNaturalApplication (HomDisj s Op h)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdSink m h = xdSinkStruct m (homomorphous h) h

xsaSink ::
  ( s ~ OrtSiteX, n ~ m+1, t ~ Star To
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisjEmpty s Op)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaSink m = do
  SomeMorphism h <- xsOrtSiteXOp
  xdSink m h

--------------------------------------------------------------------------------
-- snaDual -

snaDual :: 
  ( Transformable s Ort, TransformableGRefl Op s
  , DualisableDiagrammatic s Op Diagram t n m
  , h ~ HomEmpty s
  , t ~ Dual (Dual t)
  )
  => SomeNaturalApplication (HomDisj s Op h)
        (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m))    
  -> SomeNaturalApplication (HomDisj s Op h)
        (SDualBi (DiagramG Diagram (Dual t) n m)) (SDualBi (Diagram (Dual t) n m))
snaDual (SomeNaturalApplication h sd) = case (tauOrt (domain h), tauOrt (range h)) of
    (Struct,Struct) -> SomeNaturalApplication (h . f) sd' where
      iso :: (o ~ Op, TransformableGRefl Op s)
        => HomDisjEmpty s o x y -> IsoO s o x
      iso h = isoO (domain h)

      Contravariant2 (Inv2 t f) = iso h

      sd' = case amapG t sd of
        SDualBi (Right1 d) -> SDualBi (Left1 d)
        SDualBi (Left1 d') -> SDualBi (Right1 d') 

--------------------------------------------------------------------------------
-- xsaChainFrom -

xsaChainFrom ::
  ( s ~ OrtSiteX, n ~ m+1, t ~ Chain From
  , h ~ HomEmpty s
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisj s Op h)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaChainFrom m = amap1 snaDual $ xsaChainTo m

--------------------------------------------------------------------------------
-- xsaSource -

xsaSource ::
  ( s ~ OrtSiteX, n ~ m+1, t ~ Star From
  , h ~ HomEmpty s
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisj s Op h)
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

xsoOrtOrientation :: s ~ OrtOrientationX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoOrtOrientation
  = xOneOf [ SomeObjectClass (Struct :: Struct OrtOrientationX OS)
           , SomeObjectClass (Struct :: Struct OrtOrientationX (Op OS))
           , SomeObjectClass (Struct :: Struct OrtOrientationX (U Z))
           ]

xsOrtOrientationXOp ::  s ~ OrtOrientationX => X (SomeMorphism (HomDisjEmpty s Op))
xsOrtOrientationXOp = amap1 smCmpb2 $ xscmHomDisj xsoOrtOrientation XEmpty


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
  ( Morphism h
  , s ~ OrtOrientationX, n ~ N2, t ~ Parallel LeftToRight, Show2 h
  )
  => Any m
  -> HomDisj s Op h x y
  -> X (SomeNaturalApplication (HomDisj s Op h)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xdParallelLR m h = xdParallelLRStruct m (homomorphous h) h

xsaParallelLR ::
  ( s ~ OrtOrientationX, n ~ N2, t ~ Parallel LeftToRight
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisjEmpty s Op)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (Diagram t n m)))
xsaParallelLR m = do
  SomeMorphism h <- xsOrtOrientationXOp
  xdParallelLR m h

--------------------------------------------------------------------------------
-- xsaParallelRL -

xsaParallelRL ::
  ( s ~ OrtOrientationX, n ~ N2, t ~ Parallel RightToLeft
  )
  => Any m
  -> X (SomeNaturalApplication (HomDisjEmpty s Op)
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
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram (Chain To) (m+1) m
        chT _ = NaturalDiagrammaticSDualBi

        chF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram (Chain From) (m+1) m
        chF _ = NaturalDiagrammaticSDualBi

        skT :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram (Star To) (m+1) m
        skT _ = NaturalDiagrammaticSDualBi

        skF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram (Star From) (m+1) m
        skF _ = NaturalDiagrammaticSDualBi

        lrT :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram
               (Parallel LeftToRight) N2 m
        lrT _ = NaturalDiagrammaticSDualBi

        lrF :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticSDualBi s (HomDisjEmpty s Op) Diagram
               (Parallel RightToLeft) N2 m
        lrF _ = NaturalDiagrammaticSDualBi

