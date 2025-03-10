
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
  , RankNTypes
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
{-
    -- * Diagrammatic
    Diagrammatic(..)

    -- ** Duality
  , DiagrammaticDualisable(..)

  -- , DiagrammaticDuality(..) -- , dgmToOp, dgmFromOp

    -- * Applicative
  , DiagrammaticApplicative(..)
  , DiagrammaticFunctorial

    -- * Proposition
  , prpDiagrammaticApplicative
  , prpDiagrammaticDualisable
-}
  ) where

import Data.Typeable

import OAlg.Prelude

import OAlg.Data.Relation

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

import OAlg.Entity.Diagram hiding (DiagramDuality(..))

import OAlg.Limes.OpDuality

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m a -> Diagram t n m a

instance Diagrammatic Diagram where
  diagram = id

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
-- @'coDiagrammatic' ('tauOp' s) ('coDiagrammatic' s d) '==' 'dmap' i d@
-- for all @__t__@, @__n__@, @__m__@, @__a__@, @d@ in @__d__ __t__ __n__ __m__ __a__@,
-- @s@ in @'Struct' __s__ __a__@, @i = isoToOpOpStruct s@ and @d@ is an instance of
-- @'Eq' (__d__ __t__ __n__ __m__ __a__)@.
class ( Diagrammatic d
      , DiagrammaticFunctorial (IsoOp s) d
      , TransformableOrt s, TransformableOp s, TransformableTyp s
      ) => DiagrammaticDualisable s d where
  coDiagrammatic :: Struct s a -> d t n m a -> d (Dual t) n m (Op a)

instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => DiagrammaticDualisable s Diagram where
  coDiagrammatic = const coDiagram

--------------------------------------------------------------------------------
-- DiagrammaticDuality -

-- | duality for 'Diagrammatic' objects.
data DiagrammaticDuality s d i o a b where
  DiagrammaticDuality
    :: ( DiagrammaticDualisable s d
       , Functorial1 (IsoOp s) (d t n m)
       , Functorial1 (IsoOp s) (d (Dual t) n m)
       )
    => Dual (Dual t) :~: t
    -> DiagrammaticDuality s d (IsoOp s) Op (d t n m) (d (Dual t) n m)

instance Symmetric (DiagrammaticDuality s d i o) where
  swap (DiagrammaticDuality Refl) = DiagrammaticDuality Refl

instance (TransformableTyp s, Transformable1 Op s)
  => Duality1 s (DiagrammaticDuality s dy) (IsoOp s) Op where
  toDual1 (DiagrammaticDuality _)    = coDiagrammatic
  isoBidual1 (DiagrammaticDuality _) = Functor1 . isoToOpOpStruct   

{-
--------------------------------------------------------------------------------
-- dgmdSoundDual1 -

-- | soundness of 'Dual1' for 'DiagrammaticDuality's.
dgmdSoundDual1 :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
dgmdSoundDual1 (DiagrammaticDuality r) = diagrammaticSoundDual1 r

--------------------------------------------------------------------------------
-- DiagrammaticDuality - Duality1 -


instance TransformableDual1 (DiagrammaticDuality s d i o) where
  tauDual1 d@(DiagrammaticDuality _) = tauDual1' d

tauDual1' :: DiagrammaticDuality s d i o (d t n m)
  -> DiagrammaticDuality s d i o (Dual1 (d t n m))
tauDual1' d@(DiagrammaticDuality _) = tauDual1'' d (dgmdSoundDual1 d)

tauDual1'' :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
  -> DiagrammaticDuality s d i o (Dual1 (d t n m))
tauDual1'' (DiagrammaticDuality Refl) Refl = DiagrammaticDuality Refl


instance ReflexiveDual1 (DiagrammaticDuality s d i o) where
  reflDual1 d@(DiagrammaticDuality _) = reflDual1' d
  
reflDual1' :: DiagrammaticDuality s d i o (d t n m) -> Dual1 (Dual1 (d t n m)) :~: d t n m
reflDual1' d = reflDual1'' d (lemma1 d) (lemma3 d)

lemma1 :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m)
lemma1 d = lemma2 d (dgmdSoundDual1 d)

lemma2 :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m)
lemma2 _ Refl = Refl

lemma3 :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m
lemma3 d = lemma4 d Refl 

lemma4 :: DiagrammaticDuality s d i o (d t n m)
  -> Dual t :~: t' -> Dual1 (d t' n m) :~: d (Dual t') n m
lemma4 (DiagrammaticDuality _) = diagrammaticSoundDual1

reflDual1'' :: DiagrammaticDuality s d i o (d t n m)
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m) -- lemma1
  -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m   -- lemma3
  -> Dual1 (Dual1 (d t n m)) :~: d t n m
reflDual1'' (DiagrammaticDuality Refl) Refl Refl = Refl

instance (TransformableTyp s, Transformable1 Op s)
  => Duality1 s (DiagrammaticDuality s d) (IsoOp s) Op where
  toDual1 d@(DiagrammaticDuality _)  = case dgmdSoundDual1 d of Refl -> coDiagrammatic
  isoBidual1 (DiagrammaticDuality _) = Functor1 . isoToOpOpStruct   
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

--------------------------------------------------------------------------------
-- dgmDuality -

instance (Category h, HomOriented h) => Functorial1 h (Diagram t n m)

dgmDuality :: (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => Dual (Dual t) :~: t
  -> DiagrammaticDuality s Diagram (IsoOp s) Op (Diagram t n m) (Diagram (Dual t) n m)
dgmDuality = DiagrammaticDuality

