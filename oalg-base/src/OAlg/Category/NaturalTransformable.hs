
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
  ( -- * Transformable
    NaturalTransformable
  , NaturalTransformation(..), roh'
  , NaturalFunctorial

    -- * Natural
  , Natural(..), rohSub

    -- * Duality
  , NaturalTransformableDual1
  
    -- * Proposition
  , prpNaturalTransformableEqExt
  , prpNaturalTransformable, SomeNaturalApplication(..)
  , relNaturalTransformable
  ) where

import OAlg.Prelude 

import OAlg.Category.Unify

--------------------------------------------------------------------------------
-- Natural -

-- | natural associations on @__s__@-structured types
-- between @__f__@ and @__g__@ within @__b__@.
class Natural s b f g where
  roh :: Struct s x -> b (f x) (g x)

--------------------------------------------------------------------------------
-- rohSub -

rohSubStruct :: Natural s b f g
  => Struct v (f x) -> Struct v (g x) -> Struct (SubStruct t s) x
  -> Struct s x -> Sub v b (f x) (g x)
rohSubStruct Struct Struct Struct = Sub . roh

rohSub :: ( Natural s b f g
          , Transformable t s, TransformableG f t v, TransformableG g t v
          )
  => Struct (SubStruct t s) x -> Sub v b (f x) (g x)
rohSub t = rohSubStruct (tauGSubStruct t) (tauGSubStruct t) t (tau (tauSubStruct t)) 

instance ( Natural s b f g, Transformable t s
         , TransformableG f t v, TransformableG g t v
         )
  => Natural (SubStruct t s) (Sub v b) f g where
  roh = rohSub


--------------------------------------------------------------------------------
-- NaturalTransformable -

-- | natural generalized associations.
--
-- __Property__ Let @'NaturalTransformable' __s a b f g__@ and
-- @n@ in @'NatrualTransormation __s a b r f g__@, then holds:
--
-- (1) For all @__x__@, @__y__@ and @a@ in @__a x y__@ holds:
-- @'amapG' a '.' 'roh'' n ('domain' a) '.=.' 'roh'' n ('range' a) '.' 'amapG' a@.
class
  ( Natural s b f g
  , Transformable (ObjectClass a) s
  , Morphism a, Category b
  , ApplicativeG f a b, ApplicativeG g a b
  )
  => NaturalTransformable s a b f g


instance ( NaturalTransformable s a b f g
         , TransformableObjectClass v b
         , TransformableG f t v, TransformableG g t v
         , Transformable t s
         )
  => NaturalTransformable (SubStruct t s) (Sub t a) (Sub v b) f g 

--------------------------------------------------------------------------------
-- NaturalTransformation -

-- | witness for a 'NaturalTransformable'.
data NaturalTransformation s a b f g where
  NaturalTransformation :: NaturalTransformable s a b f g => NaturalTransformation s a b f g

--------------------------------------------------------------------------------
-- NaturalFunctorial -

-- | natural transformables admitting the functorial propperty.
type NaturalFunctorial s a b f g
  = ( NaturalTransformable s a b f g
    , FunctorialG f a b, FunctorialG g a b
    )

--------------------------------------------------------------------------------
-- NaturalTransformableDual1 -

-- | helper class to avoid undecidable instances.
class NaturalTransformable s h b (Dual1 f) (Dual1 g)
  => NaturalTransformableDual1 s h b f g
  
--------------------------------------------------------------------------------
-- roh' -

rohStruct :: NaturalTransformation s a b f g -> Struct s x -> b (f x) (g x)
rohStruct NaturalTransformation = roh

roh' :: NaturalTransformation s a b f g -> Struct (ObjectClass a) x -> b (f x) (g x)
roh' n@NaturalTransformation s = rohStruct n (tau s)

--------------------------------------------------------------------------------
-- prpNaturalTransformableEqExt -

relNaturalTransformableEqExt :: EqExt b => NaturalTransformation s a b f g -> a x y -> Statement
relNaturalTransformableEqExt n@NaturalTransformation a
  = amapG a . roh' n (domain a) .=. roh' n (range a) . amapG a

-- | validity for 'NaturalTransformable' within 'EqExt'. 
prpNaturalTransformableEqExt :: EqExt b
  => NaturalTransformation s a b f g -> X (SomeMorphism a) -> Statement
prpNaturalTransformableEqExt n xa = Prp "NaturalTransformableEqExt" :<=>:
  Forall xa (\(SomeMorphism a) -> relNaturalTransformableEqExt n a)

instance (EqExt b, XStandard (SomeMorphism a)) => Validable (NaturalTransformation s a b f g) where
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
  => NaturalTransformation s a (->) f g -> a x y -> f x -> Statement
relNaturalTransformable n@NaturalTransformation a f
  = ((amap1 a $ roh' n (domain a) f) == (roh' n (range a) $ amap1 a f))
    :?> Params ["a":=show2 a,"f x":=show f]

-- | validity according to 'NaturalTransformable' for some applications.
prpNaturalTransformable :: NaturalTransformation s a (->) f g
  -> X (SomeNaturalApplication a f g) -> Statement
prpNaturalTransformable n xsa = Prp "NaturalTransformable" :<=>:
  Forall xsa (\(SomeNaturalApplication a f) -> relNaturalTransformable n a f)



