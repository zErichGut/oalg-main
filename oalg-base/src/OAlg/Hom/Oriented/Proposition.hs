
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

-- |
-- Module      : OAlg.Hom.Oriented.Proposition
-- Description : propositions on homomorphisms between oriented structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on homomorphisms between 'Oriented' structures.
module OAlg.Hom.Oriented.Proposition
  (
    -- * Disjunctive Homomorphism
    prpHomOrientedDisjunctive

    -- * Duality
  , prpDualisableOriented

    -- * HomDisj
  , prpHomDisjOpOrt
  )
  where

import Control.Monad hiding (Functor(..))

import OAlg.Prelude

import OAlg.Category.Dualisable
import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Proxy
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented

import OAlg.Hom.Definition
import OAlg.Hom.Oriented.Definition
import OAlg.Hom.Oriented.X

--------------------------------------------------------------------------------
-- prpDualisableOriented -

-- | validity according to 'DualisableOriented'.
relDualisableOriented :: DualisableOriented s o
  => q o -> Struct s x -> Struct Ort x -> Struct Ort (o x) -> XOrt x -> Statement
relDualisableOriented q s Struct Struct xx = Forall xx
    (\x -> And [ Label "1" :<=>: ((start $ tArw x) == (tPnt $ end x)) :?> Params ["x":=show x]
               , Label "2" :<=>: ((end $ tArw x) == (tPnt $ start x)) :?> Params ["x":=show x]
               ]
    )
  where
    tArw = toDualArw q s
    tPnt = toDualPnt q s

-- | validity according to 'DualisableOriented'.
prpDualisableOriented :: DualisableOriented s o
  => q o -> Struct s x -> XOrt x -> Statement
prpDualisableOriented q s xx = Prp "DualisableOriented" :<=>:
  relDualisableOriented q s (tau s) (tau (tauO s)) xx where

--------------------------------------------------------------------------------
-- prpHomDisjOrtVariant -

relHomDisjOrtCov :: (HomOrientedDisjunctive h, Show2 h)
  => Homomorphous Ort x y -> Variant2 Covariant h x y  -> x -> Statement
relHomDisjOrtCov (Struct:>:Struct) (Covariant2 h) x = Label "Covariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtCnt :: (HomOrientedDisjunctive h, Show2 h)
  => Homomorphous Ort x y -> Variant2 Contravariant h x y  -> x -> Statement
relHomDisjOrtCnt (Struct:>:Struct) (Contravariant2 h) x = Label "Contravariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtVariant :: (HomOrientedDisjunctive h, Show2 h)
  => Either2 (Variant2 Contravariant h) (Variant2 Covariant h) x y -> x -> Statement
relHomDisjOrtVariant h x = case h of
  Right2 hCov -> relHomDisjOrtCov (tauHom (homomorphous h)) hCov x
  Left2 hCnt  -> relHomDisjOrtCnt (tauHom (homomorphous h)) hCnt x

-- | validity according to property (2) of 'HomOrientedDisjunctive'.
prpHomDisjOrtVariant :: (HomOrientedDisjunctive h, Show2 h)
  => X (SomeApplication h) -> Statement
prpHomDisjOrtVariant xsa = Prp "HomDisjOrtVariant" :<=>: Forall xsa
  (\(SomeApplication h x) -> relHomDisjOrtVariant (toVariant2 h) x
  )

--------------------------------------------------------------------------------
-- prpHomOrientedDisjunctive -

-- | validity according to 'HomOrientedDisjunctive'.
prpHomOrientedDisjunctive :: (HomOrientedDisjunctive h, Show2 h)
  => X (SomeApplication h) -> Statement
prpHomOrientedDisjunctive xa = Prp "HomOrientedDisjunctive" :<=>:
  And [ prpHomDisjOrtVariant xa
      ]


--------------------------------------------------------------------------------
-- xsoOrtX -

-- | random variable for some object classes for 'OrtX'.
xsoOrtX :: s ~ OrtX => X (SomeObjectClass (SHom s s Op (HomEmpty s)))
xsoOrtX = xOneOf [ SomeObjectClass (Struct :: Struct OrtX OS)
               , SomeObjectClass (Struct :: Struct OrtX N)
               , SomeObjectClass (Struct :: Struct OrtX (Op (OS)))
               , SomeObjectClass (Struct :: Struct OrtX (Id (OS)))
               , SomeObjectClass (Struct :: Struct OrtX (Id Z))
               ]

--------------------------------------------------------------------------------
-- prpHomDisjOpOrt -

-- | validity of @'HomDisjEmpty' 'Ort' 'Op'@ according to 'prpCategoryDisjunctive',
-- 'prpCategoryDualisable', 'prpFunctorialG' and 'prpHomOrientedDisjunctive'.
prpHomDisjOpOrt :: Statement
prpHomDisjOpOrt
  = And [ prpCategoryDisjunctive xo xfg
        , prpCategoryDualisable q xo
        , prpFunctorialG qId' xo' xfg'
        , prpFunctorialG qPt' xo' xfg'
        , prpHomOrientedDisjunctive xsa
        ] where

  q    = Proxy2 :: Proxy2 Op (HomDisjEmpty OrtX Op)
  qId' = FunctorG :: FunctorG Id (Sub OrtX (HomDisjEmpty OrtX Op)) EqualExtOrt
  qPt' = FunctorG :: FunctorG Pnt (Sub OrtX (HomDisjEmpty OrtX Op)) EqualExtOrt

  
  xo :: X (SomeObjectClass (HomDisjEmpty OrtX Op))
  xo = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xsoOrtX
  

  xo' :: X (SomeObjectClass (Sub OrtX (HomDisjEmpty OrtX Op)))
  xo' = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xo

  xfg :: X (SomeCmpb2 (HomDisjEmpty OrtX Op))
  xfg = xscmHomDisj xsoOrtX XEmpty

  xfg' :: X (SomeCmpb2 (Sub OrtX (HomDisjEmpty OrtX Op)))
  xfg' = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (sub f) (sub g)) xfg

  xsa :: X (SomeApplication (HomDisjEmpty OrtX Op))
  xsa = join
      $ amap1
          (  (\(SomeMorphism m) -> xSomeAppl m)
           . (\(SomeCmpb2 f g) -> SomeMorphism (f . g))
          )
      $ xfg
