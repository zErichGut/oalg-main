
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
  , dgmFromOpOp

  , DiagrammaticDuality(..) -- , dgmToOp, dgmFromOp

    -- * Applicative
  , DiagrammaticApplicative(..)
  , DiagrammaticFunctorial

    -- * Proposition
  , prpDiagrammaticApplicative
  , prpDiagrammaticDualisable

  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

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

instance FunctorialHomOriented h => DiagrammaticFunctorial h Diagram

--------------------------------------------------------------------------------
-- DiagrammaticDualisable -

-- | 'Op'-dualisable 'Diagrammatic' objects.
--
-- __Property__ Let @'DiagrammaticDualisable' __s__ __d__@, then holds:
-- @'coDiagrammatic' ('tauOp' s) ('coDiagrammatic' s d) '==' 'dmap' ('isoToOpOpStruct' s) d@
-- for all @__t__@, @__n__@, @__m__@, @__a__@, @d@ in @__d__ __t__ __n__ __m__ __a__@,
-- @s@ in @'Struct' __s__ __a__@ and @d@ is an instance of @'Eq' (__d__ __t__ __n__ __m__ __a__)@.
class ( Diagrammatic d
      , DiagrammaticFunctorial (IsoOp s) d
      , TransformableOrt s, TransformableOp s, TransformableTyp s
      ) => DiagrammaticDualisable s d where
  coDiagrammatic :: Struct s a -> d t n m a -> d (Dual t) n m (Op a)

instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => DiagrammaticDualisable s Diagram where coDiagrammatic _ = coDiagram

--------------------------------------------------------------------------------
-- dgmFromOpOp -

-- | from @'Op' '.' 'Op'@.
dgmFromOpOp :: DiagrammaticDualisable s d
  => Struct s a -> d t n m (Op (Op a)) -> d t n m a
dgmFromOpOp s = dmap (isoFromOpOpStruct s)

--------------------------------------------------------------------------------
-- coDiagrammaticInv -

-- | the inverse to 'coDiagrammatic'.
coDiagrammaticInv :: DiagrammaticDualisable s d => Struct s a -> Dual (Dual t) :~: t
  -> d (Dual t) n m (Op a) -> d t n m a
coDiagrammaticInv s Refl = dgmFromOpOp s . coDiagrammatic (tauOp s)

--------------------------------------------------------------------------------
-- DiagrammaticDuality -

data DiagrammaticDuality s d x y where
  DiagrammaticDuality :: DiagrammaticDualisable s d => Dual (Dual t) :~: t
    -> DiagrammaticDuality s d (d t n m) (d (Dual t) n m)

instance OpDualisable (DiagrammaticDuality s d) (Struct s) where
  opdToOp (DiagrammaticDuality _)      = coDiagrammatic
  opdFromOp (DiagrammaticDuality rt) s = coDiagrammaticInv s rt

{-
--------------------------------------------------------------------------------
-- dgmToOp -

-- | to 'Op'.
dgmToOp :: DiagrammaticDuality s d x y -> Struct s a -> x a -> y (Op a)
dgmToOp (DiagrammaticDuality _) = coDiagrammatic

--------------------------------------------------------------------------------
-- dgmFromOp -

-- | from 'Op'.
dgmFromOp :: DiagrammaticDuality s d x y -> Struct s a -> y (Op a) -> x a
dgmFromOp (DiagrammaticDuality rt) s = coDiagrammaticInv s rt
-}

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

--------------------------------------------------------------------------------
-- prpDiagrammaticDualisable -

-- | validity according to 'DiagrammaticDualisable'.
prpDiagrammaticDualisable :: ( DiagrammaticDualisable s d
                             , Eq (d t n m (Op (Op a)))
                             , Show (d t n m a)
                             )
  => Struct s a -> Dual (Dual t) :~: t -> d t n m a -> Statement
prpDiagrammaticDualisable s Refl d = Prp "DiagrammaticDualisable" :<=>:
  (coDiagrammatic (tauOp s) (coDiagrammatic s d) == dmap (isoToOpOpStruct s) d)
    :?> Params ["d":=show d]
