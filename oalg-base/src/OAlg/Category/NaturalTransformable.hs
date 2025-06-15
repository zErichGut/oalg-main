
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
-- Module      : OAlg.Category.NaturalTransformable
-- Description : natural transformable applications.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Natural transformable applications.
module OAlg.Category.NaturalTransformable
  (
    -- * Natural Transformation
    NaturalTransformable
  , Natural(..), rohEqE
  , NaturalTransformation(..), roh'
  
    -- * Proposition
  , prpNaturalTransformableEqExt
  , prpNaturalTransformable, SomeNaturalApplication(..)  
  ) where

import OAlg.Prelude

import OAlg.Category.Unify

--------------------------------------------------------------------------------
-- Natural -

-- | @__r__@-parameterized natural associations on @__s__@-structured types
-- between @__f__@ and @__g__@ within @__b__@.
class Natural s b r f g where
  roh :: r -> Struct s x -> b (f x) (g x)

--------------------------------------------------------------------------------
-- rohEqE -

rohEqEStruct :: Natural s (->) r f g
  => Struct EqE (f x) -> Struct EqE (g x)
  -> r -> Struct s x -> Sub EqE (->) (f x) (g x)
rohEqEStruct Struct Struct r s = Sub (roh r s)

-- | the induced natural association within @'Sub' 'EqE' (->)@.
rohEqE :: (Natural s (->) r f g, TransformableG f s EqE, TransformableG g s EqE)
  => r -> Struct s x -> Sub EqE (->) (f x) (g x)
rohEqE r s = rohEqEStruct (tauG s) (tauG s) r s

instance (Natural s (->) r f g, TransformableG f s EqE, TransformableG g s EqE)
  => Natural s (Sub EqE (->)) r f g where
  roh = rohEqE

--------------------------------------------------------------------------------
-- NaturalTransformable -

-- | natural generalized associations.
--
-- __Property__ Let @'NaturalTransformable' __a b r f g__@ and
-- @n@ in @'NatrualTransormation __a b r f g__@, then holds:
--
-- (1) For all @__x__@, @__y__@ and @a@ in @__a x y__@ holds:
-- @'amapG' a '.' 'roh' n ('domain' a) '.=.' 'roh' n ('range' a) '.' 'amapG' a@.
class ( Morphism a, Category b, ApplicativeG f a b, ApplicativeG g a b
      , Natural (ObjectClass a) b r f g
      )
  => NaturalTransformable a b r f g

instance ( NaturalTransformable a (->) r f g
         , TransformableG f t EqE
         , TransformableG g t EqE
         , Natural t (->) r f g
         )
  => NaturalTransformable (Sub t a) (Sub EqE (->)) r f g 

--------------------------------------------------------------------------------
-- NaturalTransformation -

-- | natural transformation between @__f__@ and @__g__@.
data NaturalTransformation a b r f g where
  NaturalTransformation :: NaturalTransformable a b r f g => r -> NaturalTransformation a b r f g

roh' :: NaturalTransformation a b r f g -> Struct (ObjectClass a) x -> b (f x) (g x)
roh' (NaturalTransformation r) = roh r

--------------------------------------------------------------------------------
-- prpNaturalTransformableEqExt -

relNaturalTransformableEqExt :: EqExt b => NaturalTransformation a b r f g -> a x y -> Statement
relNaturalTransformableEqExt n@(NaturalTransformation _) a
  = amapG a . roh' n (domain a) .=. roh' n (range a) . amapG a

-- | validity for 'NaturalTransformable' within 'EqExt'. 
prpNaturalTransformableEqExt :: EqExt b
  => NaturalTransformation a b r f g -> X (SomeMorphism a) -> Statement
prpNaturalTransformableEqExt n xa = Prp "NaturalTransformableEqExt" :<=>: Forall xa (\(SomeMorphism a) -> relNaturalTransformableEqExt n a)

instance (EqExt b, XStandard (SomeMorphism a)) => Validable (NaturalTransformation a b r f g) where
  valid n = prpNaturalTransformableEqExt n xStandard

--------------------------------------------------------------------------------
-- SomeNaturalApplication -

data SomeNaturalApplication a f g where
  SomeNaturalApplication
    :: (Show2 a, Eq (g y), Show (f x))
    => a x y -> f x -> SomeNaturalApplication a f g

--------------------------------------------------------------------------------
-- prpNatual

relNaturalTransformable :: (Show2 a, Eq (g y), Show (f x))
  => NaturalTransformation a (->) r f g -> a x y -> f x -> Statement
relNaturalTransformable n@(NaturalTransformation _) a f
  = ((amap1 a $ roh' n (domain a) f) == (roh' n (range a) $ amap1 a f))
    :?> Params ["a":=show2 a,"f x":=show f]

-- | validity according to 'NaturalTransformable' for some applications.
prpNaturalTransformable :: NaturalTransformation a (->) r f g
  -> X (SomeNaturalApplication a f g) -> Statement
prpNaturalTransformable n xsa = Prp "NaturalTransformable" :<=>: Forall xsa (\(SomeNaturalApplication a f) -> relNaturalTransformable n a f)
