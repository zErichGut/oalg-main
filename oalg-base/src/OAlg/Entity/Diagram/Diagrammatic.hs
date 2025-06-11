
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

    -- * Application
  , ApplicativeDiagrammatic, FunctorialDiagrammatic

    -- * Duality
  , SDualityDiagrammatic, CoDiagrammatic(..)
  , DiagrammaticDuality(..), dgmDuality
  , DiagrammaticOpDuality, SDualityOpDiagrammatic
  , dgmOpDuality, dgmOpDualityOrt

    -- * Proposition
  , prpApplicativeDiagrammatic
  , prpCoDiagrammatic
  , prpSDualityDiagrammatic
-}
  
{-
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

import OAlg.Category.SDuality
import OAlg.Category.Unify

import OAlg.Data.Either

import OAlg.Hom.Oriented.Definition

import OAlg.Structure.Oriented.Definition

import OAlg.Entity.Diagram.Definition
import OAlg.Entity.FinList

--------------------------------------------------------------------------------
-- Diagrammatic -

-- | object @__d__@ having an underlying 'Diagram'.
class Diagrammatic d where
  diagram :: d t n m x -> Diagram t n m x

instance Diagrammatic Diagram where diagram = id

--------------------------------------------------------------------------------
-- dgmTypeRefl -

-- | the associated 'DiagramType' is bidual.
dgmTypeRefl :: Diagrammatic d => d t n m x -> Dual (Dual t) :~: t
dgmTypeRefl = dgTypeRefl . diagram


--------------------------------------------------------------------------------
-- ApplicativeDiagrammatic -

class ( Diagrammatic d, HomDisjunctiveOriented h
      , ApplicativeS h (d t n m)
      , Dual1 (d t n m) ~ d (Dual t) n m
      , Dual (Dual t) ~ t
      )
  => ApplicativeDiagrammatic h d t n m

ff :: (Diagrammatic d, Dual1 (d t n m) ~ d (Dual t) n m)
  => SDuality (d t n m) x -> SDuality (Diagram t n m) x
ff (SDuality sd) = SDuality $ case sd of
  Right1 d -> Right1 (diagram d)
  Left1 d' -> Left1 (diagram d')

ff' :: ( Diagrammatic d, Dual1 (d t n m) ~ d (Dual t) n m
       , ShowDual1 (d t n m) x, EqDual1 (d t n m) x
       , Oriented x
       , ShowPoint (SDuality (d t n m) x)
       , ShowPoint (SDuality (Diagram t n m) x)
       , Show (d t n m x)
       , EqPoint (SDuality (d t n m) x)
       , EqPoint (SDuality (Diagram t n m) x)
       , Eq (d t n m x)
       , XStandardPoint (SDuality (d t n m) x)
       , XStandardPoint (SDuality (Diagram t n m) x)
       , XStandard (SDuality (d t n m) x)
       , XStandard (SDuality (Diagram t n m) x)
       )
  => Sub EqEOrt (->) (SDuality (d t n m) x) (SDuality (Diagram t n m) x)
ff' = Sub ff

instance (Diagrammatic d, Dual1 (d t n m) ~ d (Dual t) n m)
  => AssociativeG s (->) r (SDuality (d t n m)) (SDuality (Diagram t n m)) where
  rohG _ _ = ff
{-
instance (Diagrammatic d, Dual1 (d t n m) ~ d (Dual t) n m)
  => AssociativeG s EqualExtOrt r (SDuality (d t n m)) (SDuality (Diagram t n m)) where
  rohG _ _ = ff'
-}
--------------------------------------------------------------------------------
-- NatrualDiagrammatic -

class ApplicativeDiagrammatic h d t n m => NaturalDiagrammatic h d t n m


gg :: NaturalDiagrammatic h d t n m
    => NaturalTransformation h (->) () (SDuality (d t n m)) (SDuality (Diagram t n m))
gg = NaturalTransformation ()

instance NaturalDiagrammatic h d t n m
  => Natural h (->) r (SDuality (d t n m)) (SDuality (Diagram t n m))
  
--------------------------------------------------------------------------------
-- AssociativeG -

-- | generalized, @__s__@-structured associations between @__f__@ and @__g__@
-- within @__b__@ parameterized over @__r__@.
class AssociativeG s b r f g where
  rohG :: r -> Struct s x -> b (f x) (g x)

--------------------------------------------------------------------------------
-- Natural -

-- | natural generalized associations.
--
-- __Property__ Let @n@ be in @'NaturalTransformation' __a b r f g__@, then holds:
--
-- (1) For all @__x__@, @__y__@ and @a@ in @__a x y__@ holds:
-- @'amapG' a '.' 'roh' n ('domain' a) '.=.' 'roh' n ('range' a) '.' 'amapG' a@.
class ( Morphism a, Category b, ApplicativeG f a b, ApplicativeG g a b
      , AssociativeG (ObjectClass a) b r f g
      )
  => Natural a b r f g

-- | natural transformation between generalized applications @__f__@ and @__g__@.
data NaturalTransformation a b r f g where
  NaturalTransformation :: Natural a b r f g => r -> NaturalTransformation a b r f g

roh :: NaturalTransformation a b r f g -> Struct (ObjectClass a) x -> b (f x) (g x)
roh (NaturalTransformation r) = rohG r

relNatural :: EqExt b => NaturalTransformation a b r f g -> a x y -> Statement
relNatural n@(NaturalTransformation _) a
  = amapG a . roh n (domain a) .=. roh n (range a) . amapG a

prpNatural :: EqExt b => NaturalTransformation a b r f g -> X (SomeMorphism a) -> Statement
prpNatural n xa = Prp "Natural" :<=>: Forall xa
  (\(SomeMorphism a) -> relNatural n a)




{-
pp :: Statement
pp = prpNatural n () xa where
  n  =  NaturalTransformation
     :: NaturalTransformation () Ort (HomOrtEmpty OrtX Op) (->) SomeDiagram SomeDiagram
  xa = error "nyi"
-}




{-
prpNatural :: Natural t a b f g => a x y -> Statement
prpNatural a = error "nyi"
-}
{-
class ( ApplicativeDiagrammatic h d t n m
      , NN ObjCl h (->) (SDuality (d t n m)) (SDuality (Diagram t n m))
      )
  => NaturalDiagrammatic h d t n m

instance (HomDisjunctiveOriented h, Dual (Dual t) ~ t)
  => ApplicativeDiagrammatic h Diagram t n m

instance ()
  => NN ObjCl h (->) (SDuality (Diagram t n m)) (SDuality (Diagram t n m)) where


instance (HomDisjunctiveOriented h, Dual (Dual t) ~ t)
  => NaturalDiagrammatic h Diagram t n m


-}
{-
rel :: (EqPoint y, Eq y, ApplicativeDiagrammatic h d t n m) => h x y -> SDuality (d t n m) x -> Bool
rel h s = smap h (ff s) == ff (smap h s)

gg :: Oriented x => SDuality (Diagram t n m) x -> FinList n (Point x)
gg (SDuality sd) = case sd of
  Right1 d -> dgPoints d
  Left1 d' -> dgPoints d'

hh :: SDuality (Diagram t n m) x -> FinList m x
hh (SDuality sd) = case sd of
  Right1 d -> dgArrows d
  Left1 d' -> dgArrows d'
  
newtype FinListPnt n x = FinListPnt (FinList n (Point x))

instance HomDisjunctiveOriented h => ApplicativeG (FinListPnt n) h (->) where
  amapG h (FinListPnt ps) = FinListPnt $ amap1 (pmap h) ps
-}



{-
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
  Label "1" :<=>: case tauOrt (range h) of
    Struct -> (amap1 h . diagram) .=. (diagram . amap1 h) where
      (.=.) = prpExtensionalEqual xd 

--------------------------------------------------------------------------------
-- FunctorialDiagrammatic -

-- | functorial applications on 'Diagrammatic' objects.
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

-- | validity according to 'CoDiagrammatic'.
prpCoDiagrammatic :: (CoDiagrammatic q s i o d, Show (d t n m a))
  => q i o -> Struct s a -> X (d t n m a) -> Statement
prpCoDiagrammatic q s xd = Prp "CoDiagrammatic" :<=>:
  Label "1" :<=>: case tauOrt (sdlTau q s) of
    Struct -> (coDiagrammatic q s . diagram) .=. (diagram . coDiagrammatic q s) where
      (.=.) = prpExtensionalEqual xd 
  
--------------------------------------------------------------------------------
-- SDualityDiagrammatic -

-- | structural duality for 'Diagrammatic' objects.
--
-- __Properties__ Let @'SDualityDiagrammatic' __q s i o d t n m__@
-- and @r@ in @'Dual' ('Dual' __t__) ':~: __t__@, then holds: for all
-- @__a__@, @q@ in @__q i o__@ and @s@ in @'Struct' __s  a__@ holds: Let @s' = 'sdlTau' s@,
-- @s'' = 'sdlTau' s'@, @'Inv2' r _ = 'sdlRefl' q s@ and @'Inv2' r'' _ = 'sdlRefl' s'@ in:
--
-- (1) If @r@ matches 'Refl' then holds:
-- @'coDiagrammatic' q s' '.' 'coDiagrammatic' q s '.=.' 'amap1' r@.
--
-- (2) @'coDiagrammatic' q s'' '.' 'amap1' r '.=.' 'amap1' r'' '.' 'coDiagrammatic' q s@.
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
  => Dual (Dual t) :~: t
  -> q i o -> Struct s a -> X (d t n m a) -> Statement
prpSDualityDiagrammatic Refl q s xd = Prp "SDualityDiagrammatic" :<=>:
  And [ Label "1" :<=>: let (.=.) = prpExtensionalEqual xd in
          ((coDiagrammatic q s' . coDiagrammatic q s) .=. amap1 r)

      , Label "2" :<=>: let (.=.) = prpExtensionalEqual xd in
          ((coDiagrammatic q s'' . amap1 r) .=. (amap1 r'' . coDiagrammatic q s))
      ]
  where s'         = sdlTau q s
        s''        = sdlTau q s'
        Inv2 r _   = sdlRefl q s
        Inv2 r'' _ = sdlRefl q s'

--------------------------------------------------------------------------------
-- DiagrammaticDuality -

-- | 'SDuality1' for 'Diagrammatic' objects where 'sdlToDual1Fst' and 'sdlToDualSnd' are given by
-- 'coDiagrammatic'.
--
-- __Note__
--
-- (1) The definition of 'sdlToDualSnd' is also given by 'coDiagrammatic' under the assumption of
-- @'Dual' ('Dual' __t__) ':~:' __t__@.
--
-- (2) From the properties of 'coDiagrammatic' and the note 3 of 'SDuality1' follows, that all the
-- properties of 'SDuality1' for 'DiagrammaticDuality' holds.
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

--------------------------------------------------------------------------------
-- dgmDuality -

-- | the induced 'DiagrammaticDuality'.
dgmDuality :: DiagramDuality q s i o (Diagram t n m) (Dual1 (Diagram t n m))
  -> DiagrammaticDuality q s i o (Diagram t n m) (Diagram (Dual t) n m)
dgmDuality (DiagramDuality q r) = DiagrammaticDuality q r

--------------------------------------------------------------------------------
-- DiagrammaticOpDuality -

-- | 'DiagrmaticDuality' according to 'IsoOp'.
type DiagrammaticOpDuality s = DiagrammaticDuality OpDuality s (IsoOp s) Op

--------------------------------------------------------------------------------
-- SDualityOpDiagrammatic -

-- | 'SDualityDiagrmmatic' according to 'IsoOp'.
type SDualityOpDiagrammatic s = SDualityDiagrammatic OpDuality s (IsoOp s) Op

--------------------------------------------------------------------------------
-- dgmOpDuality -

-- | 'Op'-duality for 'Diagrammatic' objects.
dgmOpDuality :: SDualityOpDiagrammatic s d t n m
  => Dual (Dual t) :~: t -> DiagrammaticOpDuality s (d t n m) (d (Dual t) n m)
dgmOpDuality = DiagrammaticDuality OpDuality

--------------------------------------------------------------------------------
-- dgmOpDualityOrt -

-- | 'Op'-duality for 'Diagrammatic' objects on 'Ort'-structures.
dgmOpDualityOrt :: SDualityOpDiagrammatic Ort d t n m
  => Dual (Dual t) :~: t -> DiagrammaticOpDuality Ort (d t n m) (d (Dual t) n m)
dgmOpDualityOrt = dgmOpDuality

-}
