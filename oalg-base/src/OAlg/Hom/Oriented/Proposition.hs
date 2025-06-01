
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

{-    
    -- * Disjunctive Homomorphism
    prpHomDisjunctiveOriented

    -- * Duality
  , prpDualisableOriented

    -- * HomOrt
  , prpHomOrtOpEmpty
-}
  )
  where

import Control.Monad hiding (Functor(..))

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Proxy
import OAlg.Data.Identity
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented as O

import OAlg.Hom.Oriented.Definition

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

relHomDisjOrtCov :: (HomDisjunctiveOriented h, Show2 h)
  => Homomorphous Ort x y -> HVariant Covariant h x y  -> x -> Statement
relHomDisjOrtCov (Struct:>:Struct) h x = Label "Covariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtCnt :: (HomDisjunctiveOriented h, Show2 h)
  => Homomorphous Ort x y -> HVariant Contravariant h x y  -> x -> Statement
relHomDisjOrtCnt (Struct:>:Struct) h x = Label "Contravariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtVariant :: (HomDisjunctiveOriented h, Show2 h)
  => Either2 (HVariant Contravariant h) (HVariant Covariant h) x y -> x -> Statement
relHomDisjOrtVariant h x = case h of
  Right2 hCov -> relHomDisjOrtCov (tauHom (homomorphous h)) hCov x
  Left2 hCnt  -> relHomDisjOrtCnt (tauHom (homomorphous h)) hCnt x

-- | validity according to property (2) of 'HomDisjunctiveOriented'.
prpHomDisjOrtVariant :: (HomDisjunctiveOriented h, Show2 h)
  => X (SomeApplication h) -> Statement
prpHomDisjOrtVariant xsa = Prp "HomDisjOrtVariant" :<=>: Forall xsa
  (\(SomeApplication h x) -> relHomDisjOrtVariant (hVariant h) x
  )

--------------------------------------------------------------------------------
-- prpHomDisjunctiveOriented -

-- | validity according to 'HomDisjunctiveOriented'.
prpHomDisjunctiveOriented :: (HomDisjunctiveOriented h, Show2 h)
  => X (SomeApplication h) -> Statement
prpHomDisjunctiveOriented xa = Prp "HomDisjunctiveOriented" :<=>:
  And [ prpHomDisjOrtVariant xa
      ]

--------------------------------------------------------------------------------
-- prpHomOrtOpEmpty -

-- | validity of @'HomOrtOpEmpty' 'Ort'´@.
prpHomOrtOpEmpty :: Statement
prpHomOrtOpEmpty
  = And [ prpCategoryDisjunctive xo xfg
        , prpCategoryDualisable q xo
        , prpFunctorialG qId' xo' xfg'
        , prpFunctorialG qPt' xo' xfg'
        , prpHomDisjunctiveOriented xsa
        ] where

  q    = Proxy2 :: Proxy2 Op (HomOrtEmpty OrtX Op)
  qId' = FunctorG :: FunctorG Id (Sub OrtX (HomOrtEmpty OrtX Op)) EqualExtOrt
  qPt' = FunctorG :: FunctorG Pnt (Sub OrtX (HomOrtEmpty OrtX Op)) EqualExtOrt

  
  xoSct :: X (SomeObjectClass (SHom Ort OrtX Op (HomEmpty OrtX)))
  xoSct = xOneOf [ SomeObjectClass (Struct :: Struct OrtX OS)
                 , SomeObjectClass (Struct :: Struct OrtX N)
                 , SomeObjectClass (Struct :: Struct OrtX (Op (OS)))
                 , SomeObjectClass (Struct :: Struct OrtX (Id (OS)))
                 , SomeObjectClass (Struct :: Struct OrtX (Id Z))
                 ]

  xo :: X (SomeObjectClass (HomOrtEmpty OrtX Op))
  xo = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xoSct

  xo' :: X (SomeObjectClass (Sub OrtX (HomOrtEmpty OrtX Op)))
  xo' = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xo

  xfg :: X (SomeCmpb2 (HomOrtEmpty OrtX Op))
  xfg = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (HomOrt f) (HomOrt g)) $ xSctSomeCmpb2 10 xoSct XEmpty

  xfg' :: X (SomeCmpb2 (Sub OrtX (HomOrtEmpty OrtX Op)))
  xfg' = amap1 (\(SomeCmpb2 f g) -> SomeCmpb2 (sub f) (sub g)) xfg

  xsa :: X (SomeApplication (HomOrtEmpty OrtX Op))
  xsa = join
      $ amap1
          (  (\(SomeMorphism m) -> xSomeAppl m)
           . (\(SomeCmpb2 f g) -> SomeMorphism (f . g))
          )
      $ xfg



