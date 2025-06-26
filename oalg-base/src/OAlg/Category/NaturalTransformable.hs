
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
    -- * Transformable
    NaturalTransformable
  , NaturalTransformation(..), roh'

    -- * Natural
  , Natural(..), rohSub
  
    -- * Proposition
  , prpNaturalTransformableEqExt
  , prpNaturalTransformable, SomeNaturalApplication(..)
  ) where

import OAlg.Prelude 

import OAlg.Category.Unify

--------------------------------------------------------------------------------
-- Natural -

-- | @__i__@-parameterized natural associations on @__s__@-structured types
-- between @__f__@ and @__g__@ within @__b__@.
class Natural s b i f g where
  roh :: Struct s x -> i -> b (f x) (g x)

--------------------------------------------------------------------------------
-- rohSub -

rohSubStruct :: Natural s b i f g
  => Struct s x -> Struct v (f x) -> Struct v (g x)
  -> Struct (SubStruct t s) x -> i -> Sub v b (f x) (g x)
rohSubStruct s Struct Struct _ = Sub . roh s

rohSub :: ( Natural s b i f g
      , Transformable t s
      , TransformableG f t v
      , TransformableG g t v
      )
  => Struct (SubStruct t s) x -> i -> Sub v b (f x) (g x)
rohSub t = rohSubStruct (tau (tauSubStruct t)) (tauGSubStruct t) (tauGSubStruct t) t

instance ( Natural s b i f g, Transformable t s
         , TransformableG f t v, TransformableG g t v
         )
  => Natural (SubStruct t s) (Sub v b) i f g where
  roh = rohSub

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
      , Natural s b i f g, Transformable (ObjectClass a) s
      )
  => NaturalTransformable s a b i f g

instance ( NaturalTransformable s a b i f g, TransformableObjectClass v b
         , Transformable t s, TransformableG f t v, TransformableG g t v
         )
  => NaturalTransformable (SubStruct t s) (Sub t a) (Sub v b) i f g 

--------------------------------------------------------------------------------
-- NaturalTransformation -

-- | witness for a 'NaturalTransformable'.
data NaturalTransformation s a b i f g where
  NaturalTransformation :: NaturalTransformable s a b i f g => i -> NaturalTransformation s a b i f g

--------------------------------------------------------------------------------
-- roh' -

rohStruct :: NaturalTransformation s a b i f g -> Struct s x -> b (f x) (g x)
rohStruct (NaturalTransformation i) s = roh s i

roh' :: NaturalTransformation s a b i f g -> Struct (ObjectClass a) x -> b (f x) (g x)
roh' n@(NaturalTransformation _) s = rohStruct n (tau s)

--------------------------------------------------------------------------------
-- prpNaturalTransformableEqExt -

relNaturalTransformableEqExt :: EqExt b => NaturalTransformation s a b i f g -> a x y -> Statement
relNaturalTransformableEqExt n@(NaturalTransformation _) a
  = amapG a . roh' n (domain a) .=. roh' n (range a) . amapG a

-- | validity for 'NaturalTransformable' within 'EqExt'. 
prpNaturalTransformableEqExt :: EqExt b
  => NaturalTransformation s a b i f g -> X (SomeMorphism a) -> Statement
prpNaturalTransformableEqExt n xa = Prp "NaturalTransformableEqExt" :<=>:
  Forall xa (\(SomeMorphism a) -> relNaturalTransformableEqExt n a)

instance (EqExt b, XStandard (SomeMorphism a)) => Validable (NaturalTransformation s a b i f g) where
  valid n = prpNaturalTransformableEqExt n xStandard

--------------------------------------------------------------------------------
-- SomeNaturalApplication -

-- | some @f@-indexed application.
data SomeNaturalApplication a f g where
  SomeNaturalApplication
    :: (Show2 a, Eq (g y), Show (f x))
    => a x y -> f x -> SomeNaturalApplication a f g

--------------------------------------------------------------------------------
-- prpNaturalTransformable -

relNaturalTransformable :: (Show2 a, Eq (g y), Show (f x))
  => NaturalTransformation s a (->) i f g -> a x y -> f x -> Statement
relNaturalTransformable n@(NaturalTransformation _) a f
  = ((amap1 a $ roh' n (domain a) f) == (roh' n (range a) $ amap1 a f))
    :?> Params ["a":=show2 a,"f x":=show f]

-- | validity according to 'NaturalTransformable' for some applications.
prpNaturalTransformable :: NaturalTransformation s a (->) i f g
  -> X (SomeNaturalApplication a f g) -> Statement
prpNaturalTransformable n xsa = Prp "NaturalTransformable" :<=>:
  Forall xsa (\(SomeNaturalApplication a f) -> relNaturalTransformable n a f)

