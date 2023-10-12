
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Data.Number
-- Description : basic number types
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- basic number types.
module OAlg.Data.Number
  ( -- * Natural Numbers
    N, (>-), LengthN(..), takeN

    -- * Integers
  , Z(), Integer, Int, modInt, divInt

    -- * Rationals
  , Q(), (%), numerator, denominator

    -- * Enum
  , Enum(..), enum
  )
  where

import Control.DeepSeq

import Data.Ix
import qualified Data.Ratio as R

import OAlg.Control.Exception

import OAlg.Data.Canonical
import OAlg.Data.Dualisable

--------------------------------------------------------------------------------
-- enum -

-- | enumeration.
--
--  >>> enum 3 6 :: [N]
-- [3,4,5,6]
enum :: (Ord i, Enum i) => i -> i -> [i]
enum i h | h < i = []
enum i h         = i : enum (succ i) h



--------------------------------------------------------------------------------
-- divInt -

-- | division for 'Int'
divInt :: Int -> Int -> Int
divInt = div


--------------------------------------------------------------------------------
-- modInt -

-- | modulo for 'Int'.
modInt :: Int -> Int -> Int
modInt = mod

--------------------------------------------------------------------------------
-- N -

-- | natural numbers @0, 1, 2..@.
newtype N = N Integer deriving (Eq,Ord,Ix,Real,Integral,NFData)

instance Show N where
  show (N z) = show z

--------------------------------------------------------------------------------
-- takeN -

-- | takes the first @n@ elements of the list.
takeN :: N -> [a] -> [a]
takeN (N n) xs = tk n xs where
  tk i (x:xs) | 0 < i = x : tk (i-1) xs
  tk _ _              = []

--------------------------------------------------------------------------------
-- LengthN -

-- | types admitting a length.
class LengthN x where
  lengthN :: x -> N

instance LengthN [x] where
  lengthN xs = N $ toEnum $ length $ xs

--------------------------------------------------------------------------------
-- (>-) -

infixl 6 >-
  
-- | @a >- b = a - b@ if @b <= a@, otherwise a @'Undefined' "SubtrahendToBig"@ exception will be
--  thrown.
(>-) :: N -> N -> N
(N x) >- (N y) | y <= x    = N (x - y)
               | otherwise = throw $ Undefined $ "SubtrahendToBig"

--------------------------------------------------------------------------------
-- N - Instances -

instance Embeddable N Integer where
  inj (N n) = n
  
instance Projectible N Integer where
  prj n     = N $ abs $ n

instance Num N where
  N a + N b = N (a + b)
  N a - N b | b <= a    = N (a - b)
            | otherwise = throw $ Undefined $ ("subtraction on " ++ show (a,b))
  N a * N b = N (a * b) 
  negate n@(N 0) = n
  negate   (N _) = throw $ Undefined $ "negation on neutral numbers"
  abs (N n) = N n
  signum (N n) = N $ signum $ n
  fromInteger z | 0 <= z    = N $ fromInteger $ z
                | otherwise = throw $ Undefined $ ("negative integer " ++ show z)

instance Enum N where
  succ (N n) = N (n+1)
  pred (N n) | 0 < n     = N (n-1)
             | otherwise = throw $ Undefined $ "0 has no predecessor" 
  toEnum n       = fromInteger (toEnum n)
  fromEnum (N n) = fromEnum n

instance Transposable N where
  transpose = id
  
--------------------------------------------------------------------------------
-- Z -

-- | integers @ ..-1, 0, 1, 2.. @.
newtype Z = Z Integer
  deriving (Eq,Ord,Ix,Num,Enum,Integral,Real,NFData)

instance Show Z where
  show (Z z) = show z

instance Embeddable Int Z where
  inj = toEnum
  
instance Projectible Int Z where
  prj = fromEnum

instance Embeddable Integer Z where
  inj       = Z

instance Projectible Integer Z where
  prj (Z z) = z

instance Embeddable N Z where
  inj (N n) = Z n

instance Projectible N Z where
  prj (Z n)  = N $ abs $ n

instance Transposable Z where
  transpose = id
  
--------------------------------------------------------------------------------
-- Q -

-- | rational numbers @q = z'%'n@ with @'numerator' q == z@ and @'denominator' q == n@.
newtype Q = Q R.Rational
  deriving (Eq, Ord, Num, Enum, Real, RealFrac, Fractional, NFData)

instance Show Q where
  show (Q x) = if R.denominator x == 1 then show $ R.numerator $ x else show x

instance Embeddable Z Q where
  inj (Z z) = fromInteger z
  
instance Projectible Z Q where
  prj = floor

instance Embeddable N Q where
  inj (N n) = fromInteger n
  
instance Projectible N Q where
  prj    q  = N $ abs $ floor $ q

infix 7 %
-- | Forms the ratio of two integral numbers.
(%) :: Z -> N -> Q
(Z a) % (N b) = Q (a R.% b)

-- | denominator of a rational.
--
-- __Example__
-- 
-- >>> denominator (3/2)
-- 2
denominator :: Q -> N
denominator (Q x) = N (R.denominator x)

-- | numerator of a rational.
--
-- __Example__
--
-- >>> denominator (3/2)
-- 3
numerator :: Q -> Z
numerator (Q x) = Z (R.numerator x)

instance Transposable Q where
  transpose = id

