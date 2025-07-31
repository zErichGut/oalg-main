
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
  , NaturalDiagrammatic
  , NaturalDiagrammaticDualisable, drohS
  
    -- * Duality
  , DualisableDiagrammatic
  , DualityDiagrammatic

  
{-  
    -- * Natural
  , NaturalDiagrammatic
  , NaturalDiagrammaticDualisable, dmapS

    -- * Duality
  , DualisableDiagrammatic, DualityDiagrammatic(..)
  , toDualLftDgm, toDualLftDgm'
  , toDualRgtDgm, toDualRgtDgm'

    -- * Proposition
  , prpNaturalDiagrammatic
  , prpDualisableDiagrammatic
-}
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

prpNaturalDiagrammaticTrafoChain :: Statement
prpNaturalDiagrammaticTrafoChain = error "nyi"
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

instance HomOriented h => ApplicativeG (DiagramG Diagram t n m) h (->) where
  amapG h (DiagramG d) = DiagramG (amapG h d)

instance ApplicativeG (DiagramG d t n m) (HomEmpty s) c where amapG = fromHomEmpty

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
-- Diagram - DualisableGBiDual1 -

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
-- dmap -

-- | the induced mapping between the 'Diagrammatic' objects.
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
class (HomOriented h, NaturalTransformable s h (->) (DiagramG d t n m) (Diagram t n m))
  => NaturalDiagrammatic s h d t n m

relNaturalDiagrammatic :: (NaturalDiagrammatic s h d t n m, Show2 h)
  => q s h d t n m -> Homomorphous Ort x y -> h x y -> Diagram t n m x -> Statement
relNaturalDiagrammatic _ (Struct :>: Struct) h d
  = (amapG h d == dgMap h d) :?> Params ["h":=show2 h, "d":=show d]

prpNaturalDiagrammatic :: (NaturalDiagrammatic s h d t n m, Show2 h)
  => q s h d t n m -> h x y -> Diagram t n m x -> Statement
prpNaturalDiagrammatic q h d = Prp "NaturalDiagrammatic"
  :<=>: relNaturalDiagrammatic q (tauHom (homomorphous h)) h d 

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
-- drohS -

-- | natural assocition betewwn @'SDuality' ('DiagramG' __d t n m)@ and
-- @'SDuality' ('Diagram' t n m)@
drohS :: Diagrammatic d => SDuality (DiagramG d t n m) x -> SDuality (Diagram t n m) x
drohS (SDuality (Right1 d)) = SDuality (Right1 (droh d))
drohS (SDuality (Left1 d')) = SDuality (Left1 (droh d'))


instance Diagrammatic d
  => Natural s (->) (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m)) where
  roh _ = drohS

--------------------------------------------------------------------------------
-- NaturalDiagrammaticDualisable -

-- | helper class to avoid undecidible instances.
class
  ( HomOriented h
  , NaturalTransformable s h (->) (DiagramG d t n m) (Diagram t n m)
  , NaturalTransformable s h (->) (DiagramG d (Dual t) n m) (Diagram (Dual t) n m)
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammaticDualisable s h d t n m
  
instance (NaturalDiagrammaticDualisable s h d t n m, DualisableDiagrammatic s o d t n m)
  => ApplicativeG (SDuality (DiagramG d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smap h

instance (NaturalDiagrammaticDualisable s h d t n m, DualisableDiagrammatic s o d t n m, Transformable s r)
  => NaturalTransformable r (HomDisj s o h) (->)
       (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))
























{-
-- | diagrammatic objects admitting a natural transformation from
-- @'DiagramG' __d t n m__@ to @'Diagram' __t n m__@.
--
-- __Property__ Let @'NaturalDiagrammatic' __d t n m__@ then
-- for all @__x__@, @__y__@ and @h@ in @__h x y__@ holds: 
--
-- (1) @'diagram' '.' 'dmap' h '.=.' 'dgMap' h '.' 'diagram'@.
--
-- __Note__ The property above together with @'ApplicativeG' ('Diagram __t n m__) __h__ (->)@
-- and @'Transformable' ('ObjectClass' __h__)__ s__@ establish a
-- @'NaturalTransformable' __s h__ (->) ('DiagramG' __d t n m__) ('Diagram' __t n m__)@.
class (Diagrammatic d, HomOriented h, ApplicativeG (DiagramG d t n m) h (->))
  => NaturalDiagrammatic h d t n m

instance (NaturalDiagrammatic h d t n m, TransformableHom h s)
  => NaturalTransformable s h (->) (DiagramG d t n m) (Diagram t n m)

instance (Diagrammatic d, TransformableOrt s) => NaturalDiagrammatic (HomEmpty s) d t n m

--------------------------------------------------------------------------------
-- prpNaturalDiagrammatic -

relNaturalDiagrammatic :: (NaturalDiagrammatic h d t n m, Show (h x y), Show (d t n m x))
  => Homomorphous Ort x y -> h x y -> d t n m x -> Statement
relNaturalDiagrammatic (Struct :>: Struct) h d
  = (dgMap h (diagram d) == diagram (dmap h d)) :?> Params ["h":=show h,"d":=show d] 

-- | validity according to 'NaturalDiagrammatic'.
prpNaturalDiagrammatic :: (NaturalDiagrammatic h d t n m, Show (h x y), Show (d t n m x))
  => h x y -> d t n m x -> Statement
prpNaturalDiagrammatic h d = Prp "NaturalDiagrammatic"
  :<=>: relNaturalDiagrammatic (tauHom (homomorphous h)) h d

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
-- where @n@ is a whiteness in @'DualityDiagrammatic' __s o d t n m__@.
class ( Diagrammatic d
      , DualisableGBi s (->) o (DiagramG d t n m) (DiagramG d (Dual t) n m)
      , DualisableOriented s o, TransformableGRefl o s, TransformableOrt s
      , Dual1 (d t n m) ~ d (Dual t) n m, t ~ Dual (Dual t)
      ) => DualisableDiagrammatic s o d t n m

instance DualisableDiagrammatic s o d t n m => DualisableGBiDual1 s (->) o (DiagramG d t n m)

instance (DualisableOriented s o, TransformableOrt s, TransformableGRefl o s, t ~ Dual (Dual t))
  => DualisableDiagrammatic s o Diagram t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticDualisable -

-- | natural dualsiable 'Diagrammatic' objects.
class ( NaturalDiagrammatic h d t n m, NaturalDiagrammatic h d (Dual t) n m
      , Dual1 (d t n m) ~ d (Dual t) n m
      , DualisableDiagrammatic s o d t n m
      )
  => NaturalDiagrammaticDualisable s o h d t n m

instance (Diagrammatic d, DualisableDiagrammatic s o d t n m)
  => NaturalDiagrammaticDualisable s o (HomEmpty s) d t n m

--------------------------------------------------------------------------------
-- Diagrammatic - NaturalTransformable -

instance NaturalDiagrammaticDualisable s o h d t n m
  => ApplicativeG (SDuality (DiagramG d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smap h
  
instance NaturalDiagrammaticDualisable s o h d t n m
  => NaturalTransformable s (HomDisj s o h) (->)
     (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))

instance NaturalDiagrammaticDualisable s o h d t n m
  => ApplicativeG (DiagramG d t n m) (Variant2 Covariant (HomDisj s o h)) (->) where
  amapG (Covariant2 h) d = d' where SDuality (Right1 d') = amapG h (SDuality (Right1 d))

instance NaturalDiagrammaticDualisable s o h d t n m
  => NaturalDiagrammatic (Variant2 Covariant (HomDisj s o h)) d t n m

{-
--------------------------------------------------------------------------------
-- drohS -

-- | the canonical transformation,
drohS :: Diagrammatic d => SDuality (DiagramG d t n m) x -> SDuality (Diagram t n m) x
drohS (SDuality sd) = SDuality $ case sd of
  Right1 (DiagramG d) -> Right1 (diagram d)
  Left1 (DiagramG d') -> Left1 (diagram d')

instance Diagrammatic d
  => Natural s (->) (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m)) where
  roh _ = drohS

--------------------------------------------------------------------------------
-- NaturalDiagrammaticDual1 -

-- | duality for 'NaturalDiagrammatic'.
class ( NaturalDiagrammatic h d t n m
      , NaturalDiagrammatic h d (Dual t) n m
      , Dual1 (d t n m) ~ d (Dual t) n m
      )
  => NaturalDiagrammaticDual1 h d t n m

instance (Diagrammatic d, TransformableOrt s, Dual1 (d t n m) ~ d (Dual t) n m)
  => NaturalDiagrammaticDual1 (HomEmpty s) d t n m

instance (NaturalDiagrammaticDual1 h d t n m, DualisableDiagrammatic s o d t n m)
  => ApplicativeG (DiagramG d t n m) (Variant2 Covariant (HomDisj s o h)) (->) where
  amapG (Covariant2 (HomDisj h)) d = d' where SDuality (Right1 d') = smap h (SDuality (Right1 d))

--------------------------------------------------------------------------------
-- NaturalDiagrammaticS -

-- | diagrammatic objects admitting a natural transformation from
-- @'SDuality' ('DiagramG' __d t n m__)@ to @'SDuality' ('Diagram' __t n m__)@.
--
--  __Properties__ Let @'NaturalDiagrammaticS' __s o h d t n m__@,
-- @n@ be in @'NaturalDgmS' __s o h d t n m__@, then
-- for all @__x__@ and @s@ in @'Struct' __s x__@ holds:
--
-- (1) @'diagram' '.' 'toDualLftDgm' n s '.=.' 'toDualGLft' s '.' 'diagram'@.
--
-- (2) @'diagram' '.' 'toDualRgtDgm' n s '.=.' 'toDualGRgt' s '.' 'diagram'@.
--
-- __Note__ The above properties give rise to a 'NaturalTransformation' from
-- @'SDuality' ('DiagramG' __d t n m__)@ to @'SDuality' ('Diagram' __t n m__)@.
class ( NaturalDiagrammaticDual1 h d t n m
      , DualisableDiagrammatic s o d t n m
      , t ~ Dual (Dual t)
      , TransformableGRefl o s, TransformableOrt s
      , DualisableOriented s o
      )
  => NaturalDiagrammaticS s o h d t n m

instance NaturalDiagrammaticS s o h d t n m
  => ApplicativeG (SDuality (DiagramG d t n m)) (HomDisj s o h) (->) where
  amapG (HomDisj h) = smap h

instance NaturalDiagrammaticS s o h d t n m
  => NaturalTransformable s (HomDisj s o h) (->)
      (SDuality (DiagramG d t n m)) (SDuality (Diagram t n m))

instance ( Diagrammatic d
         , TransformableOrt s, TransformableGRefl o s
         , DualisableOriented s o
         , DualisableDiagrammatic s o d t n m
         , Dual1 (d t n m) ~ d (Dual t) n m
         , t ~ Dual (Dual t)
         )
  => NaturalDiagrammaticS s o (HomEmpty s) d t n m

instance NaturalDiagrammaticS s o h d t n m
  => NaturalDiagrammatic (Variant2 Covariant (HomDisj s o h)) d t n m 
-}
--------------------------------------------------------------------------------
-- dmapS -

-- | the induced application.
dmapS :: ( ApplicativeG (SDuality (DiagramG d t n m)) h (->)
         , Dual1 (d t n m) ~ d (Dual t) n m
         )
  => h x y -> SDuality (d t n m) x -> SDuality (d t n m) y
dmapS h (SDuality d) = SDuality (f d') where
  SDuality d' = amapG h (SDuality (t d))
                        
  t :: Dual1 (d t n m) ~ d (Dual t) n m
    => Either1 (Dual1 (d t n m)) (d t n m) x
    -> Either1 (Dual1 (DiagramG d t n m)) (DiagramG d t n m) x
  t (Right1 d) = Right1 (DiagramG d)
  t (Left1 d') = Left1 (DiagramG d')

  f :: Dual1 (d t n m) ~ d (Dual t) n m
    => Either1 (Dual1 (DiagramG d t n m)) (DiagramG d t n m) x
    -> Either1 (Dual1 (d t n m)) (d t n m) x
  f (Right1 (DiagramG d)) = Right1 d
  f (Left1 (DiagramG d')) = Left1 d'


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



-}
