
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

import OAlg.Entity.Diagram.Definition

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m a -> Diagram t n m a

instance Diagrammatic Diagram where diagram = id

--------------------------------------------------------------------------------
-- dgmTypeRefl -

-- | the associated 'DiagramType' is bidual.
dgmTypeRefl :: Diagrammatic d => d t n m a -> Dual (Dual t) :~: t
dgmTypeRefl = dgTypeRefl . diagram

--------------------------------------------------------------------------------
-- ApplicativeDiagrammatic -

-- | application on 'Diagrammatic' objects.
--
-- __Property__ Let @ApplicativeDiagrammatic __h__ __d__ __t__ __n__ m@, then holds:
--
-- (1) For all @__a__@, @__b__@ and @h@ in @__h__ __a__ __b__@ holds:
-- @'amap1' h '.' 'diagram' '.=.' 'diagram' '.' 'amap1' h@.
class (Diagrammatic d, Applicative1 h (d t n m), HomOriented h) => ApplicativeDiagrammatic h d t n m

instance HomOriented h => ApplicativeDiagrammatic h Diagram t n m

--------------------------------------------------------------------------------
-- prpApplicativeDiagrammatic -

-- | validity according to 'ApplicativeDiagrammatic'.
prpApplicativeDiagrammatic :: (ApplicativeDiagrammatic h d t n m, Show (d t n m a))
  => h a b -> X (d t n m a) -> Statement
prpApplicativeDiagrammatic h xd = Prp "ApplicativeDiagrammatic" :<=>:
  case tauOrt (range h) of
    Struct -> Forall xd
      (\d  -> (amap1 h (diagram d) == diagram (amap1 h d))
                :?> Params ["d":=show d]
      )

--------------------------------------------------------------------------------
-- FunctorialDiagrammatic -

type FunctorialDiagrammatic h d t n m
  = (ApplicativeDiagrammatic h d t n m, Functorial1 h (d t n m), FunctorialHomOriented h)

--------------------------------------------------------------------------------
-- CoDiagrammatic -

-- | dualisable diagrammatic objects.
--
-- __Property__ Let @'CoDiagrammatic' __d__@ then holds:
-- For all @q@ in @__q__ __i__ __o__@, @__a__@ and @s@ in @'Struct' __s__ __a__@ with
-- @'SDualityOrietned' __q__ __s__ __i__ __o__@ holds:
--
-- (1) @'diagram' '.' 'coDiagrammatic' q s = 'coDiagram' q s '.' 'diagram'@. 
class (Diagrammatic d, SDualityOriented q s i o) => CoDiagrammatic q s i o d where
  coDiagrammatic ::  q i o -> Struct s a -> d t n m a -> d (Dual t) n m (o a)

instance SDualityOriented q s i o => CoDiagrammatic q s i o Diagram where coDiagrammatic = coDiagram

--------------------------------------------------------------------------------
-- prpCoDiagrammatic -

prpCoDiagrammatic :: (CoDiagrammatic q s i o d, Show (d t n m a))
  => q i o -> Struct s a -> X (d t n m a) -> Statement
prpCoDiagrammatic q s xd = Prp "CoDiagrammatic" :<=>:
  case tauOrt (sdlTau q s) of
    Struct -> Forall xd
      (\d -> (coDiagrammatic q s (diagram d) == diagram (coDiagrammatic q s d))
               :?> Params ["d":=show d]
      )

  
--------------------------------------------------------------------------------
-- SDualityDiagrammatic -

class ( CoDiagrammatic q s i o d, FunctorialDiagrammatic i d t n m
      , FunctorialDiagrammatic i d (Dual t) n m
      )
  => SDualityDiagrammatic q s i o d t n m 

instance (SDualityOriented q s i o, FunctorialHomOriented i)
  => SDualityDiagrammatic q s i o Diagram t n m

--------------------------------------------------------------------------------
-- prpSDualityDiagrammatic -

prpSDualityDiagrammatic :: SDualityDiagrammatic q s i o d t n m
  => (Eq (d t n m (o (o a))), Eq (d (Dual t) n m (o (o (o a)))))
  => Show (d t n m a)
  => q i o -> Struct s a -> X (d t n m a) -> Statement
prpSDualityDiagrammatic q s xd = Prp "SDualityDiagrammatic" :<=>:
  And [ Forall xd
          (\d    -> case dgmTypeRefl d of
            Refl -> (coDiagrammatic q s' (coDiagrammatic q s d) == amap1 r d)
                      :?> Params ["d":=show d]
          )
      , Forall xd
          (\d -> (coDiagrammatic q s'' (amap1 r d) == amap1 r'' (coDiagrammatic q s d))
                   :?> Params ["d":=show d]
          )
      ]
  where s'         = sdlTau q s
        s''        = sdlTau q s'
        Inv2 r _   = sdlRefl q s
        Inv2 r'' _ = sdlRefl q s'

--------------------------------------------------------------------------------
-- DiagrammaticDuality -

data DiagrammaticDuality q s i o a b where
  DiagrammaticDuality
    :: SDualityDiagrammatic q s i o d t n m
    => q i o
    -> Dual (Dual t) :~: t
    -> DiagrammaticDuality q s i o (d t n m) (d (Dual t) n m)
    
instance BiFunctorial1 i (DiagrammaticDuality q s i o) where
  fnc1Fst (DiagrammaticDuality _ _) = Functor1
  fnc1Snd (DiagrammaticDuality _ _) = Functor1

instance SReflexive s i o => SDuality1 (DiagrammaticDuality q s) s i o where
  sdlToDual1Fst (DiagrammaticDuality q _)    = coDiagrammatic q
  sdlToDual1Snd (DiagrammaticDuality q Refl) = coDiagrammatic q 

ff :: DiagramDuality q s i o (Diagram t n m) (Dual1 (Diagram t n m))
  -> DiagrammaticDuality q s i o (Diagram t n m) (Diagram (Dual t) n m)
ff (DiagramDuality q r) = DiagrammaticDuality q r

{-
--------------------------------------------------------------------------------
-- ApplicativeDiagrammatic -

-- | applications on 'Diagrammatic' objects.
--
-- __Property__ For all @h@ in @__h__ __a__ __b__@ with @'ApplicativeDiagrammatic' __h__ __d__@ holds:
--
-- (1)  @'diagram' '.' 'dmap' h = 'amap1' h '.' 'diagram'@.
class (HomOriented h, Diagrammatic d) => ApplicativeDiagrammatic h d where
  dmap :: h a b -> d t n m a -> d t n m b

instance HomOriented h => ApplicativeDiagrammatic h Diagram where dmap = amap1

--------------------------------------------------------------------------------
-- prpApplicativeDiagrammatic -

-- | validity according to 'ApplicativeDiagrammatic'.
prpApplicativeDiagrammatic :: (ApplicativeDiagrammatic h d, Show (d t n m a))
  => h a b -> X (d t n m a) -> Statement
prpApplicativeDiagrammatic h xd = Prp "ApplicativeDiagrammatic" :<=>:
  case tauOrt (range h) of
    Struct -> Forall xd
      (\d  -> (diagram (dmap h d) == amap1 h (diagram d)) 
        :?> Params ["d":=show d]
      )
  
  


--------------------------------------------------------------------------------
-- prpCoDiagrammatic -

-- | validity according to 'CoDiagrammatic'.
prpCoDiagrammatic :: (CoDiagrammatic q s i o d, Show (d t n m a), Eq (d t n m (o (o a))))
  => q i o -> Struct s a -> X (d t n m a) -> Statement
prpCoDiagrammatic q s xd = Prp "CoDiagrammatic" :<=>:
  And [ case tauOrt (sdlTau q s) of
          Struct -> Forall xd
            (\d  -> (diagram (coDiagrammatic q s d) == coDiagram q s (diagram d))
                      :?> Params ["d":=show d]
            )
      , case tauOrt (sdlTau q $ sdlTau q s) of
          Struct   -> Forall xd
            (\d    -> case dgmTypeRefl d of
              Refl -> (coDiagrammatic q (sdlTau q s) (coDiagrammatic q s d) == dmap r d)
                        :?> Params ["d":=show d]    
            )
      ]
  where Inv2 r _ = sdlRefl q s
      

-}




{-
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
