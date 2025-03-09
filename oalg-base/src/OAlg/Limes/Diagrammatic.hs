
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

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

import OAlg.Entity.Diagram hiding (DiagramDuality(..))
import OAlg.Entity.Natural hiding (lemma1)

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
-- DiagrammaticSoundDual1 -

class Diagrammatic d => DiagrammaticSoundDual1 d where
  diagrammaticSoundDual1 :: p t -> Dual1 (d t n m) :~: d (Dual t) n m

instance DiagrammaticSoundDual1 Diagram where
  diagrammaticSoundDual1 _ = Refl
  
--------------------------------------------------------------------------------
-- DiagrammaticDualisable -

-- | 'Op'-dualisable 'Diagrammatic' objects.
--
-- __Property__ Let @'DiagrammaticDualisable' __s__ __d__@, then holds:
-- @'coDiagrammatic' ('coDiagrammatic' d) '==' 'dmap' i d@
-- for all @__t__@, @__n__@, @__m__@, @__a__@, @d@ in @__d__ __t__ __n__ __m__ __a__@,
-- @s@ in @'Struct' __s__ __a__@, @'Functor1' i = 'isoBidual' ('diagramDuality' d s)@ and @d@ is an instance of @'Eq' (__d__ __t__ __n__ __m__ __a__)@.
class ( DiagrammaticSoundDual1 d
      , DiagrammaticFunctorial (IsoOp s) d
      , TransformableOrt s, TransformableOp s, TransformableTyp s
      ) => DiagrammaticDualisable s d where
  diagramDuality :: Struct s a -> d t n m a -> DiagramDuality s (IsoOp s) Op (Diagram t n m)
  coDiagrammatic :: Struct s a -> d t n m a -> Dual1 (d t n m) (Op a)


instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => DiagrammaticDualisable s Diagram where
  diagramDuality     = dgDuality
  coDiagrammatic s d = toDual1 (dgDuality s d) s d


{-
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
-}
--------------------------------------------------------------------------------
-- DiagrammaticDuality -


data DiagrammaticDuality s d i o c where
  DiagrammaticDuality
    :: ( DiagrammaticDualisable s d
       -- , Functorial1 (IsoOp s) (d t n m)
       -- xo, Functorial1 (IsoOp s) (d (Dual t) n m)
       )
    => Dual (Dual t) :~: t
    -> DiagrammaticDuality s d (IsoOp s) Op (d t n m)


instance TransformableDual1 (DiagrammaticDuality s d (IsoOp s) Op) where
  tauDual1 d@(DiagrammaticDuality _) = tauDual1' d

dgmdSoundDual1 :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
dgmdSoundDual1 (DiagrammaticDuality r) = diagrammaticSoundDual1 r

tauDual1' :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> DiagrammaticDuality s d (IsoOp s) Op (Dual1 (d t n m))
tauDual1' d@(DiagrammaticDuality _) = tauDual1'' d (dgmdSoundDual1 d)

tauDual1'' :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
  -> DiagrammaticDuality s d (IsoOp s) Op (Dual1 (d t n m))
tauDual1'' (DiagrammaticDuality Refl) Refl = DiagrammaticDuality Refl


instance ReflexiveDual1 (DiagrammaticDuality s d (IsoOp s) Op) where
  reflDual1 d@(DiagrammaticDuality _) = reflDual1' d
  
reflDual1' :: DiagrammaticDuality s d (IsoOp s) Op (d t n m) -> Dual1 (Dual1 (d t n m)) :~: d t n m
reflDual1' d = reflDual1'' d (lemma1 d) (lemma3 d)

lemma1 :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m)
lemma1 d = lemma2 d (dgmdSoundDual1 d)

lemma2 :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (d t n m) :~: d (Dual t) n m
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m)
lemma2 _ Refl = Refl

lemma3 :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m
lemma3 d = lemma4 d Refl 

lemma4 :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual t :~: t' -> Dual1 (d t' n m) :~: d (Dual t') n m
lemma4 (DiagrammaticDuality _) = diagrammaticSoundDual1

reflDual1'' :: DiagrammaticDuality s d (IsoOp s) Op (d t n m)
  -> Dual1 (Dual1 (d t n m)) :~: Dual1 (d (Dual t) n m) -- lemma1
  -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m   -- lemma3
  -> Dual1 (Dual1 (d t n m)) :~: d t n m
reflDual1'' (DiagrammaticDuality Refl) Refl Refl = Refl


{-
hh 
  :: (forall (t' :: DiagramType) (n :: N') (m :: N') . p t' -> Dual1 (d t' n m) :~: d (Dual t') n m)
  -> (forall (t' :: DiagramType) (n :: N') (m :: N') . p t' -> p (Dual t'))
  -> p t -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m
hh tau p t = tau (p t)

ff :: DiagrammaticDuality s d h o (d t n m)  
  -> Dual (Dual t) :~: t
  -> Dual1 (d (Dual t) n m) :~: d (Dual (Dual t)) n m
ff t = hh ddd pt (p t) where
  p :: Dual (Dual t) :~: t -> Proxy t
  p _ = Proxy

  pt :: Proxy t -> Proxy (Dual t)
  pt _ = Proxy
  

instance ReflexiveDual1 (DiagrammaticDuality s d (IsoOp s) Op) where
  reflDual1 r@(DiagrammaticDuality u@Refl (DiagramDuality v@Refl)) = gg r u v

gg :: DiagrammaticDuality s d h o (d t n m)  
  -> Dual1 (d t n m) :~: d (Dual t) n m -> Dual (Dual t) :~: t
  -> Dual1 (d (Dual t) n m) :~: d t n m
gg = error "nyi"
     
instance (TransformableOrt s, TransformableOp s, TransformableTyp s)
  => Duality1 s (DiagrammaticDuality s d) (IsoOp s) Op where
  toDual1 (DiagrammaticDuality Refl _) = coDiagrammatic
  isoBidual1 (DiagrammaticDuality _ _) = Functor1 . isoToOpOpStruct
-}
{-
tauBidual :: forall d (t :: DiagramType) (n :: N') (m :: N')
  .  Dual (d t n m) :~: d (Dual t) n m -> Dual (Dual t) :~: t
  -> Dual (d (Dual t) n m) :~: d t n m
tauBidual = error "nyi"


{-
--------------------------------------------------------------------------------
-- DiagrammaticDuality -

data DiagrammaticDuality s d x y where
  DiagrammaticDuality :: DiagrammaticDualisable s d => Dual (Dual t) :~: t
    -> DiagrammaticDuality s d (d t n m) (d (Dual t) n m)

instance OpDualisable (DiagrammaticDuality s d) (Struct s) where
  opdToOp (DiagrammaticDuality _)      = coDiagrammatic
  opdFromOp (DiagrammaticDuality rt) s = coDiagrammaticInv s rt
-}

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
-}
