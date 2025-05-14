

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
    prpHomDisjunctiveOriented
  , prpHomDisjOrtDual
  , prpHomDisjOrtVariant

    -- * Duality
  , prpSDualisableOriented

    -- * HomOrt
  , prpHomOrtOpEmpty

  )
  where

import Control.Monad hiding (Functor(..))

import Data.Typeable

import Data.Kind

import OAlg.Prelude

import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Identity
import OAlg.Data.Proxy
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented as O

import OAlg.Hom.Oriented.Definition


--------------------------------------------------------------------------------
-- prpSDualisableOriented -

-- | validity according to 'SDualisableOriented'.
relSDualisableOriented :: SDualisableOriented r s o
  => q r o -> Struct s x -> Struct Ort x -> Struct Ort (o x) -> XOrt x -> Statement
relSDualisableOriented q s Struct Struct xx = Forall xx
    (\x -> And [ Label "1" :<=>: ((start $ tArw x) == (tPnt $ end x)) :?> Params ["x":=show x]
               , Label "2" :<=>: ((end $ tArw x) == (tPnt $ start x)) :?> Params ["x":=show x]
               ]
    )
  where
    tArw = toDualArw q s
    tPnt = toDualPnt q s

-- | validity according to 'SDualisableOriented'.
prpSDualisableOriented :: SDualisableOriented r s o
  => q r o -> Struct s x -> XOrt x -> Statement
prpSDualisableOriented q s xx = Prp "SDualisableOriented" :<=>:
  relSDualisableOriented q s (tau s) (tau (tauO s)) xx where

  tauO :: TransformableG o s s => Struct s x -> Struct s (o x)
  tauO = tauG


--------------------------------------------------------------------------------
-- prpHomDisjOrtDual -

relHomDisjOrtDual :: (HomDisjunctiveOriented o h, Eq2 h)
  => q o h -> Struct (ObjectClass h) x -> Statement
relHomDisjOrtDual q s
  = And [ Label "1" :<=>: eq2 (fromDual . toDual) (cOne s) :?> Params []
        , Label "2" :<=>: eq2 (toDual . fromDual) (cOne (tau1 s)) :?> Params []
        ]
  where Contravariant2 toDual   = homOrtToDual' q s
        Contravariant2 fromDual = homOrtFromDual' q s

-- | validity according to 'HomDisjunctiveOriented' for (1.1) and (1.2).
prpHomDisjOrtDual :: (HomDisjunctiveOriented o h, Eq2 h)
  => q o h -> X (SomeObjectClass h) -> Statement
prpHomDisjOrtDual q xso = Prp "HomDisjOrtDual" :<=>: Forall xso
  (\(SomeObjectClass s) -> relHomDisjOrtDual q s
  )

--------------------------------------------------------------------------------
-- prpHomDisjOrtVariant -

relHomDisjOrtCovariant :: (HomDisjunctiveOriented o h, Show2 h)
  => q o -> Struct (ObjectClass h) x -> Homomorphous Ort x y
  -> SVariant Covariant h x y  -> x -> Statement
relHomDisjOrtCovariant _ _ (Struct:>:Struct) h  x = Label "Covariant" :<=>:
  And [ Label "1" :<=>: (start (amap h x) == pmap h (start x)) :?> Params ["h":= show2 h, "x":=show x]
      , Label "2" :<=>: (end (amap h x) == pmap h (end x)) :?> Params ["h":= show2 h, "x":=show x]
      ]

relHomDisjOrtVariant :: (HomDisjunctiveOriented o h, Show2 h)
  => q o -> Either2 (SVariant Contravariant h) (SVariant Covariant h) x y
  -> Struct (ObjectClass h) x -> x -> Statement
relHomDisjOrtVariant q h s x = case h of
  Right2 hCov -> Label "Covariant" :<=>: relHomDisjOrtCovariant q s (tauHom (homomorphous h)) hCov x
  Left2 hCnt  -> Label "Contravariant" :<=>:
                   relHomDisjOrtVariant q (Right2 (homOrtToCovariant (q' q hCnt) s hCnt)) s x
  where q' :: forall q f (h :: Type -> Type -> Type) (o :: Type -> Type) x y
            . q o -> f h x y -> Proxy2 o h
        q' _ _ = Proxy2

-- | validity according to 'HomDisjunctiveOriented' for (2.1) and (2.2).
prpHomDisjOrtVariant :: (HomDisjunctiveOriented o h, Show2 h)
  => q o -> X (SomeApplication h) -> Statement
prpHomDisjOrtVariant q xsa = Prp "HomDisjOrtVariant" :<=>: Forall xsa
  (\(SomeApplication h x) -> relHomDisjOrtVariant q (toVariant2 h) (domain h) x
  )
 
--------------------------------------------------------------------------------
-- prpHomDisjunctiveOriented -

-- | validity according to 'HomDisjunctiveOriented'.
prpHomDisjunctiveOriented :: (HomDisjunctiveOriented o h, Show2 h, Eq2 h)
  => q o -> X (SomeObjectClass h) -> X (SomeApplication h) -> Statement
prpHomDisjunctiveOriented q xso xsa = Prp "HomDisjunctiveOriented" :<=>:
  And [ prpHomDisjOrtDual (q' q xso) xso
      , prpHomDisjOrtVariant q xsa
      ]
  where q' :: forall q (o :: Type -> Type) h . q o -> X (SomeObjectClass h) -> Proxy2 o h
        q' _ _ = Proxy2

--------------------------------------------------------------------------------
-- prpHomOrtOpEmpty -


-- | validity of @'HomOrtOpEmpty' 'Ort'´@.
prpHomOrtOpEmpty :: Statement
prpHomOrtOpEmpty
  = And [ prpCategoryDisjunctive xo xfg
        , prpFunctorialG qId xo xfg
        , prpFunctorialG qPt xo xfg
        , prpHomDisjunctiveOriented qo xo xsa
        ] where
  
  qo  = Proxy :: Proxy Op
  qId = FunctorG :: FunctorG Id (HomOrt OrtX OrtX Op (HomEmpty OrtX)) EqualExtOrt
  qPt = FunctorG :: FunctorG Pnt (HomOrt OrtX OrtX Op (HomEmpty OrtX)) EqualExtOrt
  
  xoSct :: X (SomeObjectClass (SHom OrtX OrtX Op (HomEmpty OrtX)))
  xoSct = xOneOf [ SomeObjectClass (Struct :: Struct OrtX OS)
                 , SomeObjectClass (Struct :: Struct OrtX N)
                 , SomeObjectClass (Struct :: Struct OrtX Q)
                 ]

  xo :: X (SomeObjectClass (HomOrt OrtX OrtX Op (HomEmpty OrtX)))
  xo = amap1 (\(SomeObjectClass s) -> SomeObjectClass s) xoSct

  xfg :: X (SomeCmpb2 (HomOrt OrtX OrtX Op (HomEmpty OrtX)))
  xfg = xSctSomeCmpb2 10 xoSct XEmpty

  xsa :: X (SomeApplication (HomOrt OrtX OrtX Op (HomEmpty OrtX)))
  xsa = join
      $ amap1
          (  (\(SomeMorphism m) -> xSomeAppl m)
           . (\(SomeCmpb2 f g) -> SomeMorphism (f . g))
          )
      $ xfg

