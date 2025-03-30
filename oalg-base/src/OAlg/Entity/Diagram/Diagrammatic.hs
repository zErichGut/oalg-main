
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
-- Description : objects having an underlying diagram.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Objects having an underlying 'Diagram'.
module OAlg.Entity.Diagram.Diagrammatic
  (

{-
    -- * Diagrammatic
    Diagrammatic(..), dgmTypeRefl

    -- ** Duality
  , DiagrammaticOpDualisable(..)
  , DiagrammaticOpDuality(..)
  , DiagrammaticOpDuality', dgmOpDuality

    -- * Applicative
  , DiagrammaticApplicative(..), DiagrammaticApplicative1
  , DiagrammaticFunctorial, DiagrammaticFunctorial1

    -- * Proposition
  , prpDiagrammaticApplicative
  , prpDiagrammaticApplicative1
  , prpDiagrammaticOpDualisable
-}
  ) where

import Data.Typeable

import OAlg.Prelude


import OAlg.Data.SDuality

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

import OAlg.Entity.Diagram hiding (DiagramDuality(..))

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m a -> Diagram t n m a

--------------------------------------------------------------------------------
-- Diagram - Diagrammatic -

instance Diagrammatic Diagram where diagram = id

--------------------------------------------------------------------------------
-- dgmTypeRefl -

-- | the associated 'DiagramType' is bidual.
dgmTypeRefl :: Diagrammatic d => d t n m a -> Dual (Dual t) :~: t
dgmTypeRefl = dgTypeRefl . diagram


{-
--------------------------------------------------------------------------------
-- DiagrammaticApplicative -

-- | applications on 'Diagrammatic' objects.
--
-- __Property__ Let @h@ be in @__h__ __a__ __b__@ for @'HomOriented' __h__@ and @'Diagrammatic' __d__@,
-- then holds: For all @__t__@, @__n__@, @__m__@, @__a__@ and @d@ in @__d__ __t__ __n__ __m__ __a__@
-- holds: @'diagram' ('dmap' h d) '==' 'dmap' h ('diagram' d)@.
class (HomOriented h, Diagrammatic d) => DiagrammaticApplicative h d where
  dmap :: h a b -> d t n m a -> d t n m b

instance HomOriented h => DiagrammaticApplicative h Diagram where dmap = amap1

--------------------------------------------------------------------------------
-- DiagrammaticApplicative1 -

-- | applications on 'Diagrammatic' objects as a one-parameterized type, where 'dmap' and 'amap1'
-- are equaly defined.
--
-- __Property__ Let @'DiagrammaticApplicative __h__ __d__@ and
-- @'Applicative1' __h__ (__d__ __t__ __n__ __m__)@, then holds:
-- @'dmap' h d '==' 'amap1' h d@ for all @__a__@, @__b__@, @h@ in @__h__ __a__ __b__@ and @d@ in
-- @__d__ __t__ __n__ __m__ __a__@.
class (DiagrammaticApplicative h d, Applicative1 h (d t n m)) => DiagrammaticApplicative1 h d t n m

instance HomOriented h => DiagrammaticApplicative1 h Diagram t n m

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
-- DiagrammaticFunctorial1 -

-- | functorial applications on 'Diagrammatic' objects as a one-parameterized type.
--
-- __Note__ Actually from  @'DiagrammaticApplicative1' __h__ __d__ __t__ __n__ __m__@ and
-- @'Functorial1'  __h__ (__d__ __t__ __n__ __m__)@ it follows that
-- @'DiagrammaticFunctorial __h__ __d__@ holds, but it is not feasible to declare an
-- instance:
--
-- @
-- instance (DiagrammaticApplicative1 h d t n m, Functorial1 h (d t n m))
--   => DiagrammaticFunctorial h d
-- @
type DiagrammaticFunctorial1 h d t n m
  = ( DiagrammaticApplicative1 h d t n m
    , DiagrammaticFunctorial h d
    , Functorial1 h (d t n m)
    )
    
instance FunctorialHomOriented h => DiagrammaticFunctorial h Diagram

--------------------------------------------------------------------------------
-- DiagrammaticOpDualisable -

-- | 'Op'-dualisable 'Diagrammatic' objects.
--
-- __Property__ Let @'DiagrammaticOpDualisable' __s__ __d__@, then holds:
-- @'coDiagrammatic' ('tauOp' s) ('coDiagrammatic' s d) '==' 'dmap' i d@
-- for all @__t__@, @__n__@, @__m__@, @__a__@, @d@ in @__d__ __t__ __n__ __m__ __a__@,
-- @s@ in @'Struct' __s__ __a__@, @i = isoToOpOpStruct s@ and @d@ is an instance of
-- @'Eq' (__d__ __t__ __n__ __m__ __a__)@.
class ( Diagrammatic d, DiagrammaticApplicative (IsoOp s) d) => DiagrammaticOpDualisable s d where
  coDiagrammatic :: Struct s a -> d t n m a -> d (Dual t) n m (Op a)

instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => DiagrammaticOpDualisable s Diagram where
  coDiagrammatic = const coDiagram

--------------------------------------------------------------------------------
-- DiagrammaticOpDuality -

-- | 'Op'-duality for 'Diagrammatic' objects.
data DiagrammaticOpDuality s d i o a b where
  DiagrammaticOpDuality
    :: ( DiagrammaticOpDualisable s d
       , DiagrammaticFunctorial1 (IsoOp s) d t n m
       , DiagrammaticFunctorial1 (IsoOp s) d (Dual t) n m
       )
    => Dual (Dual t) :~: t
    -> DiagrammaticOpDuality s d (IsoOp s) Op (d t n m) (d (Dual t) n m)

instance Symmetric (DiagrammaticOpDuality s d i o) where
  swap (DiagrammaticOpDuality Refl) = DiagrammaticOpDuality Refl

instance (TransformableTyp s, Transformable1 Op s)
  => Duality1 s (DiagrammaticOpDuality s d) (IsoOp s) Op where
  toDualFst (DiagrammaticOpDuality _)    = coDiagrammatic
  isoBidualFst (DiagrammaticOpDuality _) = Functor1 . isoToOpOpStruct   

--------------------------------------------------------------------------------
-- DiagrammaticOpDuality' -

-- | diagrammatic 'Op' duality.
type DiagrammaticOpDuality' s d t n m
  = DiagrammaticOpDuality s d (IsoOp s) Op (d t n m) (d (Dual t) n m)

--------------------------------------------------------------------------------
-- dgmOpDuality -

-- | 'Op'-duality for 'Diagrams's.
dgmOpDuality :: (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => Dual (Dual t) :~: t
  -> DiagrammaticOpDuality' s Diagram t n m
dgmOpDuality = DiagrammaticOpDuality


--------------------------------------------------------------------------------
-- prpDiagrammaticApplicative -

relDiagrammaticApplicative :: (DiagrammaticApplicative h d, Show (d t n m a))
  => Struct Ort b -> h a b -> d t n m a -> Statement
relDiagrammaticApplicative Struct h a
  = (diagram (dmap h a) == dmap h (diagram a)) :?> Params ["a":=show a]

-- | validity according to 'DiagrammaticApplicative'.
prpDiagrammaticApplicative :: (DiagrammaticApplicative h d, Show (d t n m a))
  => h a b -> d t n m a -> Statement
prpDiagrammaticApplicative h a = Prp "DiagrammaticApplicative" :<=>:
  relDiagrammaticApplicative (tau (range h)) h a

--------------------------------------------------------------------------------
-- prpDiagrammaticApplicative1 -

-- | validity according to 'DiagrammaticApplicative1'.
prpDiagrammaticApplicative1 :: ( DiagrammaticApplicative1 h d t n m
                               , Eq (d t n m b), Show (d t n m a)
                               )
  => h a b -> d t n m a -> Statement
prpDiagrammaticApplicative1 h d = Prp "DiagrammaticApplicative1" :<=>:
  (dmap h d == amap1 h d) :?> Params ["d":= show d]
  
--------------------------------------------------------------------------------
-- prpDiagrammaticOpDualisable -

-- | validity according to 'DiagrammaticOpDualisable'.
prpDiagrammaticOpDualisable
  :: ( DiagrammaticOpDualisable s d, Eq (d t n m (Op (Op a))), Show (d t n m a))
  => Struct s a -> Dual (Dual t) :~: t -> d t n m a -> Statement
prpDiagrammaticOpDualisable s Refl d = Prp "DiagrammaticOpDualisable" :<=>:
  (coDiagrammatic (tauOp s) (coDiagrammatic s d) == dmap (isoToOpOpStruct s) d)
    :?> Params ["d":=show d]
-}
