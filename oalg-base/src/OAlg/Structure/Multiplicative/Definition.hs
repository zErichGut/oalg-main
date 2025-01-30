
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}


-- |
-- Module      : OAlg.Structure.Multiplicative.Definition
-- Description : definition of multiplicative structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- multiplicative structures, i.e. structures with a __partially__ defined multiplication @('*')@.
module OAlg.Structure.Multiplicative.Definition
  (
    -- * Multiplicative
    Multiplicative(..), one', isOne, Mlt, TransformableMlt

    -- * Transposable
  , TransposableMultiplicative

    -- * Commutative
  , Commutative
  
    -- * Invertible
  , Invertible(..), Inv(..)

    -- * Cayleyan
  , Cayleyan

    -- * X
  , xosPathAt, xosPath, xosXOrtSitePath

  )
  where

import qualified Prelude as A

import Control.Monad
import Control.Exception

import Data.List(repeat)
import Data.Foldable

import OAlg.Control.Solver

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented

--------------------------------------------------------------------------------
-- Multiplicative -

infixl 7 *

-- | 'Oriented' structures with a __partially__ defined __multiplication__ and having
-- 'one' as the __neutral element__ of the multiplication. An entity of a
-- 'Multiplicative' structure will be called a __factor__.
--
-- __Properties__ Let __@c@__ be a type instance of the class 'Multiplicative', then
-- holds:
--
-- (1) #Mlt1#For all @p@ in  @'Point' __c__@ holds: @'orientation' ('one' p) '==' p ':>' p@.
--
-- (2) #Mlt2#For all @f@ and @g@ in __@c@__ holds:
--
--     (1) #Mlt2_1#if @'start' f '==' 'end' g@ then @f '*' g@ is 'valid' and
--     @'start' (f '*' g) '==' 'start' g@ and @'end' (f '*' g) '==' 'end' f@.
--
--     (2) #Mlt2_2#if @'start' f '/=' 'end' g@ then @f '*' g@ is not 'valid' and its
--     evaluation will end up in a 'NotMultiplicable' exception.
--
-- (3) #Mlt3#For all @f@ in __@c@__ holds:
-- @'one' ('end' f) '*' f '==' f@ and @f '*' 'one' ('start' f) '==' f@.
--
-- (4) #Mlt4#For all @f@, @g@ and @h@ in __@c@__ with @'start' g == 'end' h@
-- and @'start' f == 'end' g@ holds: @(f '*' g) '*' h '==' f '*' (g '*' h)@.
--
-- (5) #Mlt5#For all @f@ in __@c@__ holds:
--
--     (1) #Mlt5_1#@'npower' f 1 '==' f@.
--
--     (2) #Mlt5_2#If @f@ is a endo than @'npower' f 0 '==' 'one' ('start' f)@ and
--     For all @n@ in 'N' holds: @'npower' f ('succ' n) '==' f '*' 'npower' f n@.
--
-- Such a __@c@__ will be called a __/multiplicative structure/__ and an entity @f@ of
-- __@c@__ will be called __/factor/__. The associated factor @'one' p@ to a @p@ in
-- @'Point' __c__@ will be called the __/one at/__ @p@.
--
-- __Note__ If the types __@c@__ and @'Point' __c__@ are interpreted as sets
-- __@M@__ and __@O@__ and @'*'@ as a partially defined function from __@M x M -> M@__ then
-- this forms a __/small category/__ with objects in __@O@__ and morphisms in __@M@__.
class Oriented c => Multiplicative c where
  {-# MINIMAL one,(*) #-}

  -- | the neutral element associated to each point. If there is no ambiguity
  --   for @'one' p@ we will briefly denote it by @1 r@ or just @1@.
  one :: Point c -> c

  -- | the multiplication of two factors.
  (*) :: c -> c -> c
  
  -- | @n@ times the multiplication of a given factor @f@.
  npower :: c -> N -> c
  npower f 1                  = f
  npower f _ | not (isEndo f) = throw NotExponential
  npower f n                  = foldr (*) (one (start f)) $ takeN n $ repeat $ f

--------------------------------------------------------------------------------
-- Multiplicative - Instance -

instance Multiplicative () where
  one _ = ()
  _ * _ = () 
  npower _ _ = ()
  
instance Multiplicative Int where
  one _ = 1
  (*) = (A.*)

instance Multiplicative Integer where
  one _ = 1
  (*) = (A.*)

instance Multiplicative N where
  one _ = 1
  (*) = (A.*)

instance Multiplicative Z where
  one _ = 1
  (*) = (A.*)

instance Multiplicative Q where
  one _ = 1
  (*) = (A.*)

instance Entity p => Multiplicative (Orientation p) where
  one p = p :> p
  (c :> d) * (a :> b) | b == c    = a :> d
                      | otherwise = throw NotMultiplicable

  npower o 1             = o
  npower o _ | isEndo o  = o
             | otherwise = throw NotExponential

instance Oriented q => Multiplicative (Path q) where
  one = pthOne
  (*) = pthMlt

instance Multiplicative c => Multiplicative (Op c) where
  one = Op . one
  Op f * Op g = Op (g * f)
  npower (Op f) n = Op (npower f n)

--------------------------------------------------------------------------------
-- one' -

-- | the 'one' to a given point. The type @p c@ serves only as proxy and 'one'' is
-- lazy in it.
--
-- __Note__ As 'Point' may be a non-injective type family,
-- the type checker needs some times a little bit more information
-- to pic the right 'one'.
one' :: Multiplicative c => p c -> Point c -> c
one' _ = one

--------------------------------------------------------------------------------
-- isOne -

-- | check for being equal to 'one'.
isOne :: Multiplicative c => c -> Bool
isOne f = f == one (end f)

--------------------------------------------------------------------------------
-- Transposable -

-- | transposable 'Multiplicative' structures.
--
-- __Property__ Let __@c@__ be a 'TransposableMultiplicative' structure, then holds:
--
-- (1) For all @p@ in @'Point' __c__@ holds: @'transpose' ('one' p) = 'one' p@.
--
-- (2) For all @f@, @g@ in __@c@__ with @'start' f '==' 'end' g@ holds:
-- @'transpose' (f '*' g) '==' 'transpose' g '*' 'transpose' f@.
class (TransposableOriented c, Multiplicative c) => TransposableMultiplicative c

instance Entity p => TransposableMultiplicative (Orientation p)
instance TransposableMultiplicative N
instance TransposableMultiplicative Z
instance TransposableMultiplicative Q

--------------------------------------------------------------------------------
-- Commutative -

-- | commutative multiplicative structures.
--
-- __Property__ Let @__c__@ be a 'Commutative' structure, then holds: For all @f@ and @g@ in @__c__@
-- with @'start' f '==' 'end' f@, @'start' g '==' 'end' g@ and @'start' f '==' 'end' g@ holds:
-- @f '*' g '==' g '*' f@.
class Multiplicative c => Commutative c

instance Commutative ()
instance Commutative Int
instance Commutative Integer
instance Commutative N
instance Commutative Z
instance Commutative Q
instance Commutative c => Commutative (Op c)

----------------------------------------
-- Invertible - 

-- | multiplicative structures having a __/multiplicative inverse/__.
--
-- __Definition__ Let @f@ and @g@ be two factors in a 'Multiplicative' structure @___c__@
-- then we call @g@ a __/multiplicative inverse/__ to @f@ (or short inverse) if and
-- only if the following hold:
--
-- (1) @'start' g == 'end' f@ and @'end' g == 'start' f@.
--
-- (2) @f '*' g = 'one' ('end' f)@ and @g '*' f == 'one' ('start' f)@.
--
-- __Properties__ For all @f@ in a 'Invertible' structure @__c__@ holds:
--
-- (1) @'isInvertible' f@ is equivalent to @'solvable' ('tryToInvert' f)@.
--
-- (2) if @'isInvertible' f@ holds, then @'invert' f@ is 'valid' and it is the multiplicative
-- inverse of @f@. Furthermore @'invert' f '==' 'solve' ('tryToInvert' m)@.
--
-- (3) if 'not' @'isInvertible' f@ holds, then @'invert' f@ is not 'valid' and evaluating
-- it will end up in a 'NotInvertible'-exception.
--
--  __Note__
--
-- (1) It is not required that every factor has a multiplicative inverse (see 'Cayleyan'
-- for such structures).
--
-- (2) This structure is intended for multiplicative structures having a
-- known algorithm to evaluate for every invertible @f@ its inverse.
class Multiplicative c => Invertible c where
  {-# MINIMAL tryToInvert #-}
  
  -- | solver to evaluate the multiplicative inverse - if it exists.
  tryToInvert :: c -> Solver c

  -- | the inverse.
  invert :: c -> c
  invert = solve . tryToInvert

  -- | check for being invertible.
  isInvertible :: c -> Bool
  isInvertible = solvable . tryToInvert

  -- | if @0 '<=' z@ then @n@ times the multiplication for the given factor else @'prj' z@ times the
  -- multiplication of the inverse of the given factor.
  zpower :: c -> Z -> c
  zpower f z = npower f' (prj z) where f' = if z < 0 then invert f else f

instance Invertible () where
  tryToInvert _ = return ()

instance Invertible Int where
  tryToInvert n = if A.abs n == 1 then return n else failure NotInvertible

instance Invertible Integer where
  tryToInvert z = if A.abs z == 1 then return z else failure NotInvertible

instance Invertible N where
  tryToInvert n = if n == 1 then return 1 else failure NotInvertible

instance Invertible Z where
  tryToInvert z = if A.abs z == 1 then return z else failure NotInvertible

instance Invertible Q where
  tryToInvert q = if q == 0 then failure NotInvertible else return (1 A./ q)

instance Entity p => Invertible (Orientation p) where
  tryToInvert = return . transpose

instance Invertible c => Invertible (Op c) where
  tryToInvert (Op f) = fmap Op $ tryToInvert f

--------------------------------------------------------------------------------
-- Cayleyan -

-- | 'Invertible' structures where every element is invertible.
--
-- __Property__ Let @__c__@ be a 'Cayleyan' structure, then holds: For all
-- @f@ in @__c__@ holds: @'isInvertible' f '==' 'True'@.
--
-- __Note__
--
-- (1) If the type @'Point' __c__@ is singleton, then the mathematical interpretation of @__c__@
-- is a __group__.
--
-- (2) The name of this structures is given by /Arthur Cayley/ who introduced the concept
-- (and the name) of an abstract group in 1854
-- (<https://en.wikipedia.org/wiki/Arthur_Cayley>).
--
-- (3) Usually in mathematics such a structure is called a __/groupoid/__.
class Invertible c => Cayleyan c

instance Cayleyan ()
instance Entity p => Cayleyan (Orientation p)
instance Cayleyan c => Cayleyan (Op c)

--------------------------------------------------------------------------------
-- Inv -

-- | invertible factors within a 'Multiplicative' structures @__c__@, which forms a /sub/
-- 'Multiplicative' structure on @__c__@, given by the canonical inclusion 'inj' which is
-- given by @\\'Inv' f _ -> f@.
--
-- __Property__ Let @'Inv' f f'@ be in @'Inv' __c__@ where @__c__@ is a 'Multiplicative'
-- structure, then holds:
--
-- (1) @'orientation' f' '==' 'opposite' ('orientation' f)@.
--
-- (2) @f' '*' f '==' 'one' ('start' f)@.
--
-- (3) @f '*' f' '==' 'one' ('end' f)@.
--
-- __Note__ The canonical inclusion is obviously not injective on the /set/ of all values
-- of type @'Inv' __c__@ to @__c__@. But restricted to the 'valid' ones it is injective,
-- because the inverses of a @f@ in @__c__@ are uniquely determined by @f@.
data Inv c = Inv c c deriving (Show,Eq)

instance Embeddable (Inv c) c where
  inj (Inv f _) = f

instance Multiplicative c => Validable (Inv c) where
  valid (Inv f f') = Label "Inv" :<=>:
    And [ valid (f,f')
        , Label "1" :<=>: (orientation f' == opposite (orientation f)):?>prms
        , Label "2" :<=>: (f' * f == one (start f)):?>prms
        , Label "3" :<=>: (f * f' == one (end f)):?>prms
        ]
    where prms = Params ["f":=show f,"f'":=show f']

instance Multiplicative c => Entity (Inv c)

instance Multiplicative c => Oriented (Inv c) where
  type Point (Inv c) = Point c
  orientation (Inv f _) = orientation f

instance Multiplicative c => Multiplicative (Inv c) where
  one p = Inv o o where o = one p

  Inv f f' * Inv g g'
    | end g == start f = Inv (f*g) (g'*f')
    | otherwise        = throw NotMultiplicable

  npower (Inv f f') n = Inv (npower f n) (npower f' n)

instance Multiplicative c => Invertible (Inv c) where
  tryToInvert (Inv f f') = return (Inv f' f)

instance Multiplicative c => Cayleyan (Inv c)

instance TransposableMultiplicative c => Transposable (Inv c) where
  transpose (Inv f f') = Inv (transpose f) (transpose f')

instance TransposableMultiplicative c => TransposableOriented (Inv c)
instance TransposableMultiplicative c => TransposableMultiplicative (Inv c)

--------------------------------------------------------------------------------
-- Mlt -
  
-- | type representing the class of 'Multiplicative' structures.
data Mlt

type instance Structure Mlt x = Multiplicative x

instance Transformable Mlt Typ where tau Struct = Struct
instance Transformable Mlt Ent where tau Struct = Struct
instance Transformable Mlt Ort where tau Struct = Struct
instance Transformable1 Op Mlt where tau1 Struct = Struct
instance TransformableOp Mlt

--------------------------------------------------------------------------------
-- TransformableMlt -

-- | transformable to 'Multiplicative' structure.
class (Transformable s Ort, Transformable s Mlt) => TransformableMlt s

instance TransformableTyp Mlt
instance TransformableOrt Mlt
instance TransformableMlt Mlt


--------------------------------------------------------------------------------
-- xosAdjOne -

-- | adjoining a 'one' for empty random variable.
xosAdjOne :: Multiplicative c => XOrtSite s c -> XOrtSite s c
xosAdjOne xs@(XStart xp _) = XStart xp (xq' xs) where
  xq' :: Multiplicative c => XOrtSite From c -> Point c -> X c
  xq' (XStart _ xc) p = case xc p of
    XEmpty -> return $ one p
    xf     -> xf
xosAdjOne xe@(XEnd _ _) = fromDual $ xosAdjOne $ toDual xe

--------------------------------------------------------------------------------
-- xosPathAt -

-- | random variable of paths at the given point and the given length (see 'xosPathMaxAt' and as
-- @__c__@ is 'Multiplicative', the underlying random variable for factors for a given point is
-- not empty).
xosPathAt :: Multiplicative c => XOrtSite s c -> N -> Point c -> X (Path c)
xosPathAt xa = xosPathMaxAt (xosAdjOne xa)

--------------------------------------------------------------------------------
-- xosPath -

-- | random variable of paths with the given length.
xosPath :: Multiplicative c => XOrtSite s c -> N -> X (Path c)
xosPath xa = xosPathMax (xosAdjOne xa)

--------------------------------------------------------------------------------
-- dstPathDrcn -

-- | puts the distribution.
dstPathDrcn :: Multiplicative c => Int -> N -> XOrtSite s c -> IO ()
dstPathDrcn n l xa = getOmega >>= putDistribution n (fmap show xx) where
  xx = xosPoint xa >>= xosPathAt xa l

--------------------------------------------------------------------------------
-- xosXOrtSitePath -

-- | the induced random variable for paths.
xosXOrtSitePath :: Multiplicative c
  => XOrtSite s c -> N -> XOrtSite s (Path c)
xosXOrtSitePath xs@(XStart xp _) n = XStart xp (xosPathAt xs n)
xosXOrtSitePath xe@(XEnd xp _) n = XEnd xp (xosPathAt xe n)
