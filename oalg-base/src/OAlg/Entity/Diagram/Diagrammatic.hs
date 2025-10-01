
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds, ConstraintKinds #-}

-- |
-- Module      : OAlg.Entity.Diagram.Diagrammatic
-- Description : objects with a naturally underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- objects with a naturally underlying 'Diagram'. They serve to generalize the concept of
-- limits according to a diagram (see "OAlg.Limes.Limits").
module OAlg.Entity.Diagram.Diagrammatic
  (
    -- * Diagrammatic
    Diagrammatic(..)
  , DiagramG(..), dmap
  , sdbToDgmObj, sdbFromDgmObj

    -- * Natural
    
  , NaturalDiagrammatic
  , drohS
  , NaturalDiagrammaticW

    -- * Duality
  , NaturalDiagrammaticBi

  , prpNaturalDiagrammatic
{-  
    -- * Proposition
  , prpDiagrammatic
-}
  ) where

import Control.Monad

import Data.Typeable

import OAlg.Prelude

import OAlg.Category.NaturalTransformable
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

-- | wrapper for 'Diagrammatic'-objects.
newtype DiagramG d (t :: DiagramType) (n :: N') (m :: N') x = DiagramG (d t n m x)
  deriving (Show,Eq)

type instance Dual1 (DiagramG d t n m) = DiagramG d (Dual t) n m

instance Oriented x => ShowDual1 (DiagramG Diagram t n m) x
instance Oriented x => EqDual1 (DiagramG Diagram t n m) x

instance Validable (d t n m x) => Validable (DiagramG d t n m x) where
  valid (DiagramG d) = valid d

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
droh :: Diagrammatic d => DiagramG d t n m x -> DiagramG Diagram t n m x
droh (DiagramG d) = DiagramG (diagram d)

instance Diagrammatic d => Natural s (->) (DiagramG d t n m) (DiagramG Diagram t n m) where
  roh _ = droh

--------------------------------------------------------------------------------
-- sdbToDgmObj -

-- | canonical mapping to its underlying diagrammatic object.
sdbToDgmObj :: Dual1 (d t n m) ~ d (Dual t) n m
  => SDualBi (DiagramG d t n m) x -> SDualBi (d t n m) x
sdbToDgmObj (SDualBi (Right1 (DiagramG d))) = SDualBi (Right1 d)
sdbToDgmObj (SDualBi (Left1 (DiagramG d'))) = SDualBi (Left1 d')

--------------------------------------------------------------------------------
-- sdbFromDgmObj -

-- | canonical mapping from its underlying diagrammatic object.
sdbFromDgmObj :: Dual1 (d t n m) ~ d (Dual t) n m
  => SDualBi (d t n m) x -> SDualBi (DiagramG d t n m) x
sdbFromDgmObj (SDualBi (Right1 d)) = SDualBi (Right1 (DiagramG d))
sdbFromDgmObj (SDualBi (Left1 d')) = SDualBi (Left1 (DiagramG d'))

--------------------------------------------------------------------------------
-- drohS -

-- | natural assocition induced by 'droh' betewwn @'SDualBi' ('DiagramG' __d t n m__)@ and
-- @'SDualBi' ('Diagram' __t n m__)@.
drohS :: Diagrammatic d => SDualBi (DiagramG d t n m) x -> SDualBi (DiagramG Diagram t n m) x
drohS (SDualBi (Right1 d)) = SDualBi (Right1 (droh d))
drohS (SDualBi (Left1 d')) = SDualBi (Left1 (droh d'))

instance Diagrammatic d
  => Natural s (->) (SDualBi (DiagramG d t n m)) (SDualBi (DiagramG Diagram t n m)) where
  roh _ = drohS

--------------------------------------------------------------------------------
-- NaturalDiagrammatic -

-- | natural transformation on 'Diagrammatic' objects from @'SDualBi' ('DiagramG' __d t n m__)@ to
-- @'SDualBi' ('Diagram' __t n m__)@, respecting the canonical application of @__h__@ on
-- @'SDualBi' ('Diagram' __t n m__)@.
--
-- __Property__ Let @'NaturalDiagrammatic' __s h d t n m__@, then for all @__x__@,
-- @__y__@ and @h@ in @__h x y__@ holds:
--
-- (1) @'amapG' h '.=.' dgMapS h@.
--
-- __Note__ This property is required if incoherent instances are permitted.
class
  ( Diagrammatic d
  , CategoryDisjunctive h
  , HomOrientedDisjunctive h
  , FunctorialOriented h
  , NaturalTransformable h (->) (SDualBi (DiagramG d t n m)) (SDualBi (DiagramG Diagram t n m))
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammatic h d t n m

--------------------------------------------------------------------------------
-- Diagram -

instance
  ( HomOrientedDisjunctive h
  , t ~ Dual (Dual t)
  )
  => ApplicativeG (SDualBi (DiagramG Diagram t n m)) h (->) where
  amapG h = sdbFromDgmObj . amapG h . sdbToDgmObj

instance
  ( HomOrientedDisjunctive h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => FunctorialG (SDualBi (DiagramG Diagram t n m)) h (->)

instance
  ( HomOrientedDisjunctive h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalTransformable h (->) (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m))

instance
  ( CategoryDisjunctive h
  , HomOrientedDisjunctive h
  , FunctorialOriented h
  , t ~ Dual (Dual t)
  )
  => NaturalDiagrammatic h Diagram t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticW -

-- | whiteness of a 'NaturalDiagrammatic'.
data NaturalDiagrammaticW h d t n m where
  NaturalDiagrammaticW :: NaturalDiagrammatic h d t n m
    => NaturalDiagrammaticW h d t n m

--------------------------------------------------------------------------------
-- NaturalDiagrammaticBi -

-- | natural diagrammatic for @__t__@ and @'Dual' __t__@.
type NaturalDiagrammaticBi h d t n m =
  ( NaturalDiagrammatic h d t n m
  , NaturalDiagrammatic h d (Dual t) n m
  )


--------------------------------------------------------------------------------
-- prpNaturalDiagrammatic -

-- | validity according to 'NatrualDiagrammatic'.
prpNaturalDiagrammatic :: NaturalDiagrammatic h d t n m
  => q h d t n m
  -> X (SomeNaturalApplication h (SDualBi (DiagramG d t n m)) (SDualBi (DiagramG Diagram t n m)))
  -> Statement
prpNaturalDiagrammatic q xsa = Prp "NaturalDiagrammatic"
  :<=>: Forall xsa (\(SomeNaturalApplication h d)
                    -> And [ relNaturalTransformable (n q) h d
                           ]
                   )
  where n :: NaturalDiagrammatic h d t n m
          => q h d t n m
          -> NaturalTransformation h (->)
               (SDualBi (DiagramG d t n m)) (SDualBi (DiagramG Diagram t n m))
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
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
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
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xdChainTo m h = xdChainToStruct m (homomorphous h) h

xsaChainTo ::(n ~ m+1, t ~ Chain To)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m))
       )
xsaChainTo m = do
  SomeMorphism h <- xsOrtSiteXOp
  xdChainTo m h

--------------------------------------------------------------------------------
-- xsaSink -

xdSinkStruct :: (n ~ m+1, t ~ Star To, Show2 h)
  => Any m
  -> Homomorphous OrtSiteX x y 
  -> h x y
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
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
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xdSink m h = xdSinkStruct m (homomorphous h) h

xsaSink ::(n ~ m+1, t ~ Star To)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xsaSink m = do
  SomeMorphism h <- xsOrtSiteXOp
  xdSink m h

--------------------------------------------------------------------------------
-- snaDual -

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
        (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m))    
  -> SomeNaturalApplication (HomTest s)
        (SDualBi (DiagramG Diagram (Dual t) n m)) (SDualBi (Diagram (Dual t) n m))
snaDual (SomeNaturalApplication h sd) = case (tauOrt (domain h), tauOrt (range h)) of
    (Struct,Struct) -> SomeNaturalApplication (h . f) sd' where

      Contravariant2 (Inv2 t f) = isoHomTest h

      sd' = case amapG t sd of
        SDualBi (Right1 d) -> SDualBi (Left1 d)
        SDualBi (Left1 d') -> SDualBi (Right1 d') 
{-
--------------------------------------------------------------------------------
-- xsaChainFrom -

xsaChainFrom :: (n ~ m+1, t ~ Chain From)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xsaChainFrom m = amap1 snaDual $ xsaChainTo m

--------------------------------------------------------------------------------
-- xsaSource -

xsaSource ::(n ~ m+1, t ~ Star From)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtSiteX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
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
  -> X (SomeNaturalApplication h (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
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
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xdParallelLR m h = xdParallelLRStruct m (homomorphous h) h

xsaParallelLR ::(n ~ N2, t ~ Parallel LeftToRight)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtOrientationX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xsaParallelLR m = do
  SomeMorphism h <- xsOrtOrientationXOp
  xdParallelLR m h

--------------------------------------------------------------------------------
-- xsaParallelRL -

xsaParallelRL ::(n ~ N2, t ~ Parallel RightToLeft)
  => Any m
  -> X (SomeNaturalApplication (HomTest OrtOrientationX)
         (SDualBi (DiagramG Diagram t n m)) (SDualBi (DiagramG Diagram t n m)))
xsaParallelRL m = amap1 snaDual $ xsaParallelLR m

--------------------------------------------------------------------------------
-- prpDiagrammtic -

-- | validity according to 'NaturalDiagrmmaticS' for some @'HomDisjEmpty' 'OrtSiteX' 'Op'@
-- acting on some 'Diagram's.
prpDiagrammatic :: N -> Statement
prpDiagrammatic nMax = Prp "Diagrammatic"
  :<=>: And [ Forall (xNB 0 nMax)
                (\m -> case someNatural m of
                  SomeNatural m' -> And [ prpNaturalDiagrammatic (chT m') (xsaChainTo m')
                                        , prpNaturalDiagrammatic (chF m') (xsaChainFrom m')
                                        , prpNaturalDiagrammatic (skT m') (xsaSink m')
                                        , prpNaturalDiagrammatic (skF m') (xsaSource m')
                                        , prpNaturalDiagrammatic (lrT m') (xsaParallelLR m')
                                        , prpNaturalDiagrammatic (lrF m') (xsaParallelRL m')
                                        ]
                )
            ]
  where chT :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram (Chain To) (m+1) m
        chT _ = NaturalDiagrammaticW

        chF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram (Chain From) (m+1) m
        chF _ = NaturalDiagrammaticW

        skT :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram (Star To) (m+1) m
        skT _ = NaturalDiagrammaticW

        skF :: s ~ OrtSiteX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram (Star From) (m+1) m
        skF _ = NaturalDiagrammaticW

        lrT :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram
               (Parallel LeftToRight) N2 m
        lrT _ = NaturalDiagrammaticW

        lrF :: s ~ OrtOrientationX
          => Any m -> NaturalDiagrammaticW (HomTest s) Diagram
               (Parallel RightToLeft) N2 m
        lrF _ = NaturalDiagrammaticW
-}
