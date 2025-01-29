
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Category.Definition
-- Description : definition of categories
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- categories of morphisms. We adapted the concept of categories form 'Control.Category.Category' to
-- better cover our needs.
module OAlg.Category.Definition
  ( 
    -- * Category
    Category(..), cOne'

    -- | __Some basic definitions in the category @('->')@__
  , id
  , const
  , curry, uncurry, fst, snd
  , curry3, uncurry3

    -- * Cayleyan
  , Cayleyan2(..)
  
    -- * Morphism
  , Morphism(..)
  , Homomorphous(..), tauHom, tau1Hom
  , eqlDomain, eqlRange
  , eqlMorphism
  -- , toOp2Struct

    -- * Applicative
  , Applicative(..), ($)
  , Applicative1(..)
  
    -- * Functorial
  , Functorial
  , Functorial1

    -- * Forget
  , Forget(..)

    -- * Transformables
  , TransformableObjectClassTyp
  
    -- * Embeddable
  , EmbeddableMorphism
  , EmbeddableMorphismTyp
  )
  where

import Data.Type.Equality
import Data.Typeable
import Data.Kind
import Data.Maybe
import Data.List ((++))

import OAlg.Data.Show
import OAlg.Data.Equal

import OAlg.Data.Opposite
import OAlg.Data.Either

import OAlg.Category.Applicative

import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- Defs -

-- | the identity map.
id :: x -> x
id = \x -> x

-- | the constant map given by a value in @__b__@.
--
-- __Property__ Let @y@ be in @__b__@ then for all @x@ in @__a__@ holds: @'const' y x@ is identical
-- to @y@.
const :: b -> a -> b
const b _ = b

-- | the first component of the pair.
fst :: (a,b) -> a
fst (a,_) = a

-- | the second component of the pair. 
snd :: (a,b) -> b
snd (_,b) = b

-- | currying a map.
curry :: ((a,b) -> c) -> a -> b -> c
curry f a b = f (a,b)

-- | uncurrying a map.
uncurry :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

-- | currying a map.
curry3 :: ((a,b,c) -> d) -> a -> b -> c -> d
curry3 f a b c = f (a,b,c)

-- | uncurrying a map.
uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (a,b,c) = f a b c

--------------------------------------------------------------------------------
-- eqlDomain -

-- | gets for two 'Typeable' types @__x__@ and @__x'__@ and for two parameterized types maybe an
-- attest that the domain types are equal.
eqlDomain :: Struct Typ x -> Struct Typ x'
  -> m x y -> m x' y -> Maybe (x :~: x')
eqlDomain Struct Struct _ _ = eqT

--------------------------------------------------------------------------------
-- eqlRange -

-- | gets for two 'Typeable' types @__y__@ and @__y'__@ and for two parameterized types maybe an
-- attest that the range types are equal.
eqlRange :: Struct Typ y -> Struct Typ y'
  -> m x y -> m x y' -> Maybe (y :~: y')
eqlRange Struct Struct _ _ = eqT

--------------------------------------------------------------------------------
-- eqlMorphism -

-- | gets maybe an attest that the two given morphisms types are equal. 
eqlMorphism :: Typeable m
  => Struct Typ x -> Struct Typ x'
  -> Struct Typ y -> Struct Typ y'
  -> m x y -> m x' y' -> Maybe (m x y :~: m x' y')
eqlMorphism Struct Struct Struct Struct _ _ = eqT

--------------------------------------------------------------------------------
-- Homomorphous -

infix 5 :>:

-- | attest that both @__x__@ and @__y__@ have homomorphous structures, i.e.
--   both admit the same constraints given by the parameter @s@.
data Homomorphous s x y = Struct s x :>: Struct s y deriving (Show,Eq)

instance Show2 (Homomorphous m)
instance Eq2 (Homomorphous m)

--------------------------------------------------------------------------------
-- tauHom -

-- | transforming homomorphous structural attests. 
tauHom :: Transformable s t => Homomorphous s x y -> Homomorphous t x y
tauHom (d :>: r) = tau d :>: tau r

--------------------------------------------------------------------------------
-- tau1Hom -

-- | transforming homomorphous structural attests. 
tau1Hom :: Transformable1 f s => Homomorphous s x y -> Homomorphous s (f x) (f y)
tau1Hom (sx:>:sy) = tau1 sx :>: tau1 sy

--------------------------------------------------------------------------------
-- Morphism -

-- | morphism.
class Morphism m where
  {-# MINIMAL homomorphous | (domain,range) #-}

  -- | the object class.
  type ObjectClass m

  -- | attests, that the types @__x__@ and @__y__@ fulfill the constraints given
  -- by @'Homomorphous' ('ObjectClass' __m__) __x__ __y__@, i.e both fulfill the constraints
  -- given by @'Structure' ('ObjectClass' __m__) __x__@ and @'Structure' ('ObjectClass' __m__) __y__@
  -- respectively.
  homomorphous :: m x y -> Homomorphous (ObjectClass m) x y
  homomorphous m = domain m :>: range m

  -- | attests that the domain type @__x__@ fulfills the constraints given
  -- by @'Structure' ('ObjectClass' __m__) __x__@.
  domain :: m x y -> Struct (ObjectClass m) x
  domain m = d where d :>: _ = homomorphous m

  -- | attests that the range type @__y__@ fulfills the constraints given
  -- by @'Structure' ('ObjectClass' __m__) __y__@.
  range  :: m x y -> Struct (ObjectClass m) y
  range m = r where _ :>: r = homomorphous m

--------------------------------------------------------------------------------
-- toOp2Struct -

-- | transforming a 'Struct' where __@p@__ serves only as a proxy for __@m@__ and will not
--   be evaluated.
toOp2Struct :: p m -> Struct (ObjectClass m) x -> Struct (ObjectClass (Op2 m)) x
toOp2Struct _ = id

--------------------------------------------------------------------------------
-- Morphism - Instance -

instance Morphism (Homomorphous s) where
  type ObjectClass (Homomorphous s) = s
  homomorphous = id

instance Morphism (->) where
  type ObjectClass (->) = Type
  homomorphous _ = Struct :>: Struct

instance Morphism h => Morphism (Op2 h) where
  type ObjectClass (Op2 h) = ObjectClass h
  domain (Op2 h) = range h
  range (Op2 h) = domain h
  
--------------------------------------------------------------------------------
-- Category -
infixr 9 .
-- | category of morphisms.
--
--   __Properties__ Let __@c@__ be a type instance of the class 'Category', then
--   holds:
--
--  (1) #Cat1#For all types __@x@__, __@y@__ and @f@ in __@c@__ __@x@__ __@y@__ holds:
--      @'cOne' ('range' f) '.' f = f@ and @f '.' 'cOne' ('domain' f) = f@.
--
--  (1) #Cat2#For all types __@w@__, __@x@__, __@y@__, __@z@__
--      and @f@ in __@c@__ __@x@__ __@w@__, @g@ in __@c@__ __@y@__ __@x@__,
--      @h@ in __@c@__ __@z@__ __@y@__ holds: @f '.' (g '.' h) = (f '.' g) '.' h@. 
class Morphism c => Category c where
  -- | the identity morphism for an eligible __@x@__.
  cOne :: Struct (ObjectClass c) x -> c x x
  (.) :: c y z -> c x y -> c x z

--------------------------------------------------------------------------------
-- cOne' -

-- | the 'cOne' to a given @'Struct' ('ObjectClass' __c__)@. The type @__p c__@ serves only as
--   proxy and 'cOne'' is lazy in it.
--
--   __Note__ As 'ObjectClass' may be a non-injective type family,
--   the type checker needs some times a little bit more information
--   to pic the right 'cOne'.
cOne' :: Category c => p c -> Struct (ObjectClass c) x -> c x x
cOne' _ = cOne

--------------------------------------------------------------------------------
-- Category - Instance -

instance Category (Homomorphous s) where
  cOne s = s :>: s
  (Struct :>: c) . (a :>: Struct) = a:>:c

instance Category (->) where
  cOne Struct = \x -> x
  f . g = \x -> f (g x)

instance Category c => Category (Op2 c) where
  cOne s = Op2 (cOne s)
  Op2 f . Op2 g = Op2 (g . f)
  
--------------------------------------------------------------------------------
-- Functorial -

-- | representable categories, i.e. covariant functors from an 'Applicative' category
--   __c__ to @('->')@.
--
--   __Properties__ Let __@c@__ be a type instance of the class 'Functorial' then holds:
--
--   (1) #Fnc1#For all types __@x@__ and @d@ in @'Struct' ('ObjectClass' __c__) __x__@ holds:
--   @'amap' ('cOne' d) = 'id'@.
--
--   (1) #Fnc2#For all types __@x@__, __@y@__, __@z@__ and @f@ in __@c@__ __@y@__ __@z@__,
--   @g@ in __@c@__ __@x@__ __@y@__ holds: @'amap' (f '.' g) = 'amap' f '.' 'amap' g@. 
class (Applicative c, Category c) => Functorial c

--------------------------------------------------------------------------------
-- Functorial1 -

-- | representable categories, i.e. covariant functors from an 'Applicative1' category @__c__@ to
-- @('->')@.
--
-- __Properties__ Let the pair @(__c__,__f__)@ be a type instance of 'Functorial1', then holds:
--
-- (1) For all types @__x___@ and @d@ in @'Struct' ('ObjectClass' __c__) __x__@ holds:
-- @'amap1' ('cOne' d) = 'id'@.
--
-- (2) For all types @__x__@, @__y__@, @__z__@, @f@ in @__c__ __y__ __z__@ and
-- @g@ in @__c__ __x__ __y__@ holds: @'amap1' (f '.' g) = 'amap1' f '.' 'amap1' g@.
class (Category c, Applicative1 c f) => Functorial1 c f 

--------------------------------------------------------------------------------
-- Cayleyan2 -

-- | category of isomorphisms.
--
--  __Property__ Let __@c@__ be a type instance of 'Cayleyan2', then holds:
--  For all types __@x@__, __@y@__ and @f@ in __@c@__ __@x@__ __@y@__ holds:
--  @('invert2' f '.' f) == 'cOne' ('domain' f)@ and
--  @(f '.' 'invert2' f) == 'cOne' ('range' f)@ where @(==) = 'eq2'@.
class (Category c, Eq2 c) => Cayleyan2 c where
  invert2 :: c x y -> c y x

--------------------------------------------------------------------------------
-- Cayleyan2 - Instance -

instance Cayleyan2 (Homomorphous m) where
  invert2 (d :>: r) = r :>: d  

instance Cayleyan2 c => Cayleyan2 (Op2 c) where
  invert2 (Op2 f) = Op2 (invert2 f)
  
--------------------------------------------------------------------------------
-- Either2 - Morphism -

instance (Morphism f, Morphism g, ObjectClass f ~ ObjectClass g)
  => Morphism (Either2 f g) where
  
  type ObjectClass (Either2 f g) = ObjectClass f
  
  domain (Left2 f) = domain f
  domain (Right2 g) = domain g

  range (Left2 f) = range f
  range (Right2 g) = range g

--------------------------------------------------------------------------------
-- Forget -

-- | forgets the 'ObjectClass' of __@m@__ and sets it to __@t@__, under the condition
--   that the 'ObjectClass' of __@m@__ is 'Transformable' to __@t@__.
data Forget t m x y where
  Forget :: Transformable (ObjectClass m) t => m x y -> Forget t m x y

instance Show2 m => Show2 (Forget t m) where
  show2 (Forget m) = "Forget[" ++ show2 m ++ "]"
  
instance Show2 m => Show (Forget t m x y) where
  show = show2

instance Eq2 m => Eq2 (Forget t m) where
  eq2 (Forget f) (Forget g) = eq2 f g

instance Eq2 m => Eq (Forget t m x y) where
  (==) = eq2
  
instance Morphism m => Morphism (Forget t m) where
  type ObjectClass (Forget t m) = t

  homomorphous (Forget m) = tauHom (homomorphous m)

instance Applicative m => Applicative (Forget t m) where
  amap (Forget h) = amap h

--------------------------------------------------------------------------------
--

-- | helper class to avoid undecided instances.
--
-- __Example__ By declaring an instance
-- @instance (..,'Transformable' ('ObjectClass' m) 'Typ',..) => C m@ for a @'Morphism' __m__@
-- and a class @__C__@ one will get the compiler error:
--
-- @
--    • Illegal use of type family ‘ObjectClass’
--        in the constraint ‘Transformable (ObjectClass m) Typ’
--      (Use UndecidableInstances to permit this)
-- @
-- To avoid this error use this instance declaration:
-- @instance (..,'TransformableObjectClassTyp' m),..) => C m@ which will solve the problem!
class Transformable (ObjectClass m) Typ => TransformableObjectClassTyp m

--------------------------------------------------------------------------------
-- EmbeddableMorphism -

-- | morphism for which its object class can be embedded into the given structure.
class (Morphism m, Transformable (ObjectClass m) t) => EmbeddableMorphism m t

instance (Morphism m, Transformable s t) => EmbeddableMorphism (Forget s m) t

instance EmbeddableMorphism m t => EmbeddableMorphism (Op2 m) t

--------------------------------------------------------------------------------
-- EmbeddableMorphismType -

-- | helper class to avoid undecidable instances.
class EmbeddableMorphism m Typ => EmbeddableMorphismTyp m

instance (Morphism m, TransformableTyp t) => EmbeddableMorphismTyp (Forget t m)

instance EmbeddableMorphismTyp m => EmbeddableMorphismTyp (Op2 m)
