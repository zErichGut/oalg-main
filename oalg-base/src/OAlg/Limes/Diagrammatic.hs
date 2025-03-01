
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
#-}


-- |
-- Module      : OAlg.Limes.Diagrammatic
-- Description : objects having an underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Objects having an underlying 'Diagram'.
module OAlg.Limes.Diagrammatic
  (
    -- * Diagrammatic
    Diagrammatic(..)

    -- ** Duality
  , DiagrammaticDualisable(..), coDiagrammaticInv

    -- * Applicative
  , DiagrammaticApplicative(..)
  , DiagrammaticFunctorial
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented

import OAlg.Entity.Diagram

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m a -> Diagram t n m a

instance Diagrammatic Diagram where diagram = id

--------------------------------------------------------------------------------
-- DiagrammaticApplicative -

-- | applications on 'Diagrammatic' objects.
--
-- __Property__ Let @h@ be in @__h__ __a__ __b__@ for @'HomOriented' __h__@ and @'Diagrammatic' __d__@,
-- then holds: For all @__t__@, @__n__@, @__m__@, @__a__@ and @d@ in @__d__ __t__ __n__ __m__ __a__@
-- holds: @'diagram' ('dmap' h d) '==' 'dgMap' h ('diagram' d)@.
class (HomOriented h, Diagrammatic d) => DiagrammaticApplicative h d where
  dmap :: h a b -> d t n m a -> d t n m b

instance HomOriented h => DiagrammaticApplicative h Diagram where dmap = dgMap

--------------------------------------------------------------------------------
-- DiagrammaticFunctorial -

-- | functorial applications on 'Diagrammatic' objects.
--
-- __Property__ Let @'DiagrammaticFunctorial' __h__ __d__@, then holds:
--
-- (1) For all @__x__@ and @s@ in @'Struct' ('Objectclass' h) __x__@ holds:
-- @'dmap' ('cOne' s) d '==' d@ for all @__t__@, @__n__@, @__m__@ and
-- @d@ in @__d__ __t__ __n__ __m__ __x__@. 
--
-- (2) For all @__x__@, @__y__@, @__z__@, @f@ in @__h__ __y__ __x__@ and @g@ in @__h__ __x__ __y__@
-- holds: @'dmap' (f '.' g) d '==' 'dmap' f ('dmap' g d)@ for all @__t__@, @__n__@, @__m__@ and
-- @d@ in @__d__ __t__ __n__ __m__ __x__@. 
class (FunctorialHomOriented h, DiagrammaticApplicative h d) => DiagrammaticFunctorial h d

--------------------------------------------------------------------------------
-- DiagrammaticDualisable -

-- | 'Op'-dualisable 'Diagrammatic' objects.
--
-- __Property__ 
class (DiagrammaticFunctorial (IsoOp Ort) d, Diagrammatic d) => DiagrammaticDualisable d where
  coDiagrammatic :: d t n m a -> d (Dual t) n m (Op a)

diagrammaticFromOpOp :: (DiagrammaticDualisable d, Oriented a)
  => d t n m (Op (Op a)) -> d t n m a
diagrammaticFromOpOp = dmap isoFromOpOpOrt

coDiagrammaticInv :: (DiagrammaticDualisable d, Oriented a) => Dual (Dual t) :~: t
  -> d (Dual t) n m (Op a) -> d t n m a
coDiagrammaticInv Refl = diagrammaticFromOpOp . coDiagrammatic

--------------------------------------------------------------------------------
-- prpDiagrammaticApplicative -

relDiagrammaticApplicative :: (DiagrammaticApplicative h d, Show (d t n m a))
  => Struct Ort b -> h a b -> d t n m a -> Statement
relDiagrammaticApplicative Struct h a
  =  (diagram (dmap h a) == dgMap h (diagram a)) :?> Params ["a":=show a]

-- | validity according to 'DiagrammaticApplicative'.
prpDiagrammaticApplicative :: (DiagrammaticApplicative h d, Show (d t n m a))
  => h a b -> d t n m a -> Statement
prpDiagrammaticApplicative h a = Prp "DiagrammaticApplicative" :<=>:
  relDiagrammaticApplicative (tau (range h)) h a



