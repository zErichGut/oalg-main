
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Structure.Number.Definition
-- Description : definition of numbers as ordered semi rings with infinitely many elements
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- definition of numbers as ordered 'Semiring' with infinitely many elements.
module OAlg.Structure.Number.Definition
  (
    -- * Number
    Number(..), zFloor

    -- | digital represenation of numbers
  , toDigits, Digits(..)
  , toDigitsFinite, fromDigits
  , dgsBase, dgsProxy, dgsFrcTake

    -- * Integral
  , Integral(..), primes

    -- * Acyclic
  , Acyclic(..)

    -- * Fractional
  , Fractional

    -- * Measurable
  , Measurable(..)
  )
  where

import qualified Prelude as A

import Data.Proxy

import OAlg.Prelude

import OAlg.Data.TypeLits
import OAlg.Data.Canonical

import OAlg.Structure.Oriented.Definition
import OAlg.Structure.Multiplicative.Definition
import OAlg.Structure.Additive.Definition
import OAlg.Structure.Distributive.Definition
import OAlg.Structure.Ring.Definition

--------------------------------------------------------------------------------
-- Number -

-- | ordered commutative semi ring where v'+' and v'*' respect the given ordering.
--
-- __Definitions__
--
-- (1) A number @x@ is called __/positive/__ if @0 < x@ and __/negative/__ if @x < 0@.
--
-- (2) A number structure is called __/positive/__ if it contains no negative elements.
--
-- __Properties__
--
-- (1) @1@ is positive.
--
-- (2) For all @x < y@ and @z@ holds: @x v'+' z < y v'+' z@
--
-- (3) For all @0 < x@, @0 < y@ holds: @0 < x v'*' y@.
--
-- (4) For all @x@ holds: @x == 'signum' x v'*' 'abs' x@.
--
-- (5) For all @x@ holds: @'floor' x  v'+' 'fraction' x == x@.
--
-- __Note__
--
-- (1) A not positive structure of numbers contain always also the additive inverse of @1@
-- which is negative.
--
-- (2) Structures of numbers have infinitely many values, because from the
-- properties above follows that
-- @0 < 1 < 2 < .. < 'ntimes' n 1 < 'ntimes' (n v'+' 1) 1 < .. @ for all @0 <= n@.
class (Semiring r, Commutative r, Ord r) => Number r where
  {-# MINIMAL minusOne, zFloorFraction #-}

  -- | the additive inverse of @1@ - if it exists - and will be
  --   denoted by @-1@ (see the note above).
  minusOne :: Maybe r

  -- | sign of a number.
  --
  -- __Property__ For all @x@ holds: if @0 < x@ then @signum x == 1@ and if @x == 0@
  -- then @signum x == 0@ and if @x < 0@ then @signum x == -1@ (for @-1@ see @'minusOne'@).
  --
  -- __Note__ The default implementation is:
  --
  -- @
  -- signum x = case rZero `compare` x of
  --              GT -> rOne
  --              EQ -> rZero
  --              LT -> e where Just e = minusOne
  -- @
  signum :: r -> r
  signum x = case rZero `compare` x of
             GT -> rOne
             EQ -> rZero
             LT -> e where Just e = minusOne
             
  -- | absolute value of a number.
  --
  -- __Definition__ The __/absolute value/__ of a @x@ is defined by
  -- @abs x = 'signum' x v'*' x@ (which serves as the default implementation).
  --
  -- __Properties__ For all @x@ holds:
  --
  -- (1) @0 <= abs x@.
  --
  -- (2) if @0 <= x@ then @abs x == x@.
  abs :: r -> r
  abs x = signum x * x

  -- | floor of a value of a number.
  --
  -- __Properties__
  --
  -- (1) @floor 0 == 0@.
  --
  -- (2) For all @x@ holds: @floor (x v'+' 1) = floor x v'+' 1@.
  floor :: r -> r
  floor x = ntimes (prj $ fst $ zFloorFraction $ x) (signum x)

  -- | fractional part of a number.
  --
  -- __Property__ For all @x@ holds: 0 <= fraction x < 1.
  fraction :: r -> r
  fraction = snd . zFloorFraction

  -- | simultaneous evaluation of @'floor'@ - represented as an integer - and its
  -- @'fraction'@.
  --
  -- __Properties__ For all @x@ holds:
  --
  -- (1) @'floor' x == 'ntimes' ('prj' '$' fst '$' 'zFloorFraction' '$' x) ('signum' x)@.
  --
  -- (2) @'fraction' x == 'snd' '.' 'zFloorFraction'@.
  --
  -- __Note__ This properties are used for the default implementation of @'floor'@
  -- and @'fraction'@.
  zFloorFraction :: r -> (Z,r)

--------------------------------------------------------------------------------
-- zFloor -

-- | floor to 'Z'.
zFloor :: Number r => r -> Z
zFloor = fst. zFloorFraction

--------------------------------------------------------------------------------
-- Number - Instances -

instance Number N where
  minusOne          = Nothing
  abs             n = n
  signum          n = if n == 0 then 0 else 1
  floor           n = n
  fraction        _ = 0
  zFloorFraction  n = (inj n, 0)  
  
instance Number Integer where
  minusOne         = Just (-1)
  abs              = A.abs
  signum           = A.signum
  floor          z = z
  fraction       _ = 0
  zFloorFraction z = (inj z,0)

instance Number Z where
  minusOne         = Just (-1)
  abs              = A.abs
  signum           = A.signum
  floor          z = z
  fraction       _ = 0
  zFloorFraction z = (z,0)

instance Number Q where
  minusOne       = Just (-1)
  abs            = A.abs
  signum         = A.signum
  floor  q       = A.floor q % 1
  zFloorFraction = A.properFraction

--------------------------------------------------------------------------------
-- Integral -

-- | discrete numbers.
--
-- __Property__ For all @x@ holds: @'fraction' x '==' 0@.
class Number a => Integral a where
  {-# MINIMAL divMod #-}

  divMod :: a -> a -> (a,a)

  div :: a -> a -> a
  div a b = fst (divMod a b)

  mod :: a -> a -> a
  mod a b = snd (divMod a b)

instance Integral N where
  divMod = A.divMod
  div    = A.div
  mod    = A.mod
  
instance Integral Z where
  divMod = A.divMod
  div    = A.div
  mod    = A.mod
  
--------------------------------------------------------------------------------
-- primes 

-- | the list of prime numbers.
primes :: [N]
primes = filterPrime [2..]
  where filterPrime (p:xs) = p : filterPrime [x | x <- xs, x `mod` p /= 0]

--------------------------------------------------------------------------------
-- Acyclic -

-- | distributive structure with entities scaleable by 'Q'.
--
-- __Property__ For every @0 '<' n@ and point @p@ holds: @'ntimes' n ('one' p)@ is
-- invertible.
--
-- __Note__
--
-- (1) The cyclic rings @'OAlg.Entity.Commutative.Mod' n@ for @2 <= n@ are not scaleable by
-- @'Q'@, because @1 '/=' 0@ and @'ntimes' n 1 '==' 0@!
--
-- (2) If for every point @p@ holds that @'zero' (p':>'p) '==' 'one' p@ then the structure
-- is scaleable by 'Q' (e.g. @'Orientation' p@).
class (Distributive a, Abelian a, Invertible a) => Acyclic a where
  
  -- | @'qtimes' q a '==' 'ztimes' z a v'*' 'invert' ('ntimes' n ('one' ('start' a)))@.
  --   where @z = 'numerator' q@ and @n = 'denominator' q@.
  qtimes :: Q -> a -> a
  qtimes q a = ztimes z a * invert (ntimes n (one (start a)))
    where z = numerator q
          n = denominator q

instance Acyclic () where
  qtimes _ _ = ()
  
instance Acyclic Q where
  qtimes = (*)
  
--------------------------------------------------------------------------------
-- Fractional -

-- | continuous numbers, i.e acyclic and negateable numbers. They induce a sub
--   @'Q'@-vectorial structures of the real numbers.
--
--   __Note__ We will distinguish here instances of @'Fractional'@ and the mathematical
--   entities of real numbers! 
type Fractional r = (Number r, Abelian r, Acyclic r)

--------------------------------------------------------------------------------
-- Measurable -

-- | measurable entities.
class (Entity a, Number r) => Measurable a r where

  -- | distance of two points.
  --
  --   __Properties__ Let @__a__@ @__r__@ be 'Measurable', then holds:
  --
  --   (1) For all @x@ and @y@ in @__a__@ holds: @0 <= dist x y@
  --
  --   (2) For all @x@ and @y@ in @__a__@ holds: @dist x y == 0@ if and only if @x == y@.
  --
  --   (3) For all @x@ and @y@ in @__a__@ holds: @dist x y == dist y x@.
  --
  --   (4) For all @x@, @y@ and @z@ in @__a__@ holds: @dist x z@ <= @dist x y@ v'+' @dist y z@
  dist :: a -> a -> r

instance (Number r, Abelian r) => Measurable r r where
  dist a b = abs (b - a)

instance Measurable N Z where
  dist a b = inj $ A.abs $ (b A.- a)

----------------------------------------
-- Digits -

-- | digital representation of numbers for the given base @b@.
--
-- __Note__
--
-- (1) 'dgsFlr' is a finite list
--
-- (2) 'dgsFrc' maybe a infinite list and as such 'valid' could end up in an
-- infinite proposition!
data Digits (b :: Nat) r where
  Digits :: 2 <= b
    => { dgsSig :: r    -- ^ the signum.
       , dgsFlr :: [N]  -- ^ the digital representation of the floor part
       , dgsFrc :: [N]  -- ^ the digital representation of the fractional part
       }
    -> Digits b r

deriving instance Show r => Show (Digits b r)
deriving instance Eq r => Eq (Digits b r)
deriving instance Ord r => Ord (Digits b r)

instance Validable r => Validable (Digits b r) where
  valid (Digits r n m) = And [valid r,valid n,valid m]
  
--------------------------------------------------------------------------------
-- dgsProxy -

-- | the proxy with the same type @b@.
dgsProxy :: Digits b r -> Proxy b
dgsProxy _ = Proxy 

--------------------------------------------------------------------------------
-- dgsBase -

-- | the base of a digit, i.e. the corresponding natural number of the type literal @b@.
dgsBase :: KnownNat b => Digits b r -> N
dgsBase = prj . natVal . dgsProxy

--------------------------------------------------------------------------------
-- dgsFrcTake -

-- | limits the fractional part 'dgsFrc' to the length of @n@.
dgsFrcTake :: N -> Digits b r -> Digits b r
dgsFrcTake n (Digits r flr frc) = Digits r flr (takeN n $ frc)

--------------------------------------------------------------------------------
-- toDigits -
-- | the digital representation of @x@ in the base @b@.
--
--   Let @'Digits' s xs ys = 'toDigits' r@ then
--
--   * @s@ is the @'signum' x@.
--
--   * @xs@ is the digital representation of @'abs' ('floor' x)@ .
--
--   * @ys@ is the - possibly infinite - digital representation of @'abs' ('fraction' x)@
--     in the base @b@.
--
--   __Examples__
--
-- >>> toDigits (1/3) :: Digits 10 Q
-- Digits 1 [] [3,3,3..]
--
-- >>> toDigits (-4/3) :: Digits 3 Q
-- Digits (-1) [1] [1]
--
-- __Note__ To get the first @n@ digits of the fractional part @ys@ for the digital
-- representation of @x@ use @'toDigitsFinite' n x@.
toDigits :: (Number r, KnownNat b, 2 <= b) => r -> Digits b r
toDigits x = res
  where res   = Digits sig (dgtsFlr z []) (dgtsFrc f)
        base  = dgsBase res
        sig   = signum x
        (z,f) = zFloorFraction $ abs x
          
        zbs          = inj base
        dgtsFlr t ds = if t == rZero then ds else dgtsFlr z' ds'
          where (z',zn) = divMod t zbs
                ds'     = prj zn : ds
          
        dgtsFrc frc = if frc == rZero then [] else prj flr : dgtsFrc frc'
          where (flr,frc') = zFloorFraction (ntimes base frc)

--------------------------------------------------------------------------------
-- toDigitsFinite -

-- | @toDigitsFinite n@ is like 'toDigits' but the fractional part is limited to the
-- length of @n@ and is given by @'dgsFrcTake' n '.' 'toDigits'@.
toDigitsFinite :: (Number r, KnownNat b, 2 <= b) => N -> r -> Digits b r
toDigitsFinite n = dgsFrcTake n . toDigits

--------------------------------------------------------------------------------
-- fromDigits -

-- | @fromDigits n dgs\@('Digits' s xs ys)@ is given by
--   @s v'*' (xm v'*' b'^'m v'+' .. v'+' xi v'*' b'^'i v'+' .. v'+' x0 v'*' b'^'0  v'+' y1 v'*' r'^'1 v'+' .. v'+' yj v'*' r'^'j v'+' .. v'+' yn v'*' r'^'n@
-- where @b = 'dgsBase' dgs@, @xs = [xm..xi..x0]@, @ys = [y1,y2..yj..yn..]@
-- and @r = 'invert' b@.
--
-- __Property__ Let @1 '<' b@ and @dgs = 'Digits' s xs ys@ where @s@ is either 1 or -1
-- and @0 v'<=' xi '<' b@ for all @i@ and @0 v'<=' yj '<' b@ for all @j@
-- then for all @n@ holds: @'toDigits' b n ('fromDigits' b n dgs) '==' dgs@.
--
-- __Note__
--
-- (1) All the elements of the above formula are lifted to the type @r@ via
-- @\\x -> 'ntimes' x 'rOne'@.
--
-- (2) Because the type @r@ is acyclic, the expression @'invert' b@ - which is actually
-- @'invert' ('ntimes' b 'rOne')@ - is regular.
--
-- (3) If @b@ is not bigger then 1 then an exception 'Undefined' will be thrown.
fromDigits :: (Number r, Acyclic r, KnownNat b) => N -> Digits b r -> r
fromDigits n dgs@(Digits s flr frc)
  = s * (rFlr b' flr rZero + rFrc br br (takeN n frc) rZero) where
    b  = dgsBase dgs
    b' = ntimes b rOne
    br = invert b'
        -- invert b' is regular, because r is acyclic!!
        
    rFlr :: Number r => r -> [N] -> r -> r
    rFlr _ []     r = r
    rFlr x (d:ds) r = rFlr x ds (x * r + ntimes d rOne)

    rFrc :: Number r => r -> r -> [N] -> r -> r
    rFrc _  _ [] r    = r
    rFrc x y (d:ds) r = rFrc x z ds (r + y * ntimes d rOne) where z = x*y
