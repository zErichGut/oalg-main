
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.AbelianGroup.Euclid
-- Description : basic algorithms for integers
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- basic algorithms for the integers 'Z'.
module OAlg.AbelianGroup.Euclid
  ( gcd, gcds, lcm, lcms, euclid, mod0, (//)
  )
  where

import OAlg.Prelude hiding ((//))

import Data.List (foldl)

import OAlg.Data.Canonical

import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number


--------------------------------------------------------------------------------
-- mod0 -

-- | extended modulo in 'Z' according to 'N'.
--
-- __Property__ For all @z@ and @n@ holds
--
-- (1) @'mod0' z 0 '==' z@.
--
-- (2) if @0 < n@ than @'mod0' z n '==' 'mod' z ('inj' n)@.
mod0 :: Z -> N -> Z
mod0 z 0 = z
mod0 z n = mod z (inj n)

--------------------------------------------------------------------------------
-- (//) -

infix 7 //

-- | extended division in 'Z' by a dividend in 'N'.
--
--  __Properties__ For all @z@ and @n@ holds:
--
--  (1) @0 // 0 '==' 1@.
--
--  (2) if @z '/=' 0@ then @z // 0 '==' 0@.
--
--  (3) if @0 '<' n@ then @z // n '==' 'div' z n@.
--
--  (4) @z '==' (z // n) '*' 'inj' n '+' 'mod0' z n@.
(//) :: Z -> N -> Z
0 // 0 = 1
_ // 0 = 0
z // n = div z (inj n)

--------------------------------------------------------------------------------
-- euclid -

-- | extended euclidean algorithm to determine the greatest cowmon divisor.
--
-- __Properties__ @(g,s,t) = 'euclid' a b@ then
--
-- (1) @g@ is the greatest common divisor of @a@ and @b@.
--
-- (2) @g '==' s '*' a '+' t '*' b@.
euclid :: Z -> Z -> (N,Z,Z)
  -- we use the property: signum x * x == abs x for all x :: Z
euclid a b = (prj r,signum a * s,signum b * t) where
  (r,s,t) = eval (abs a,1,0) (abs b,0,1)

 -- invariants for eval (r'',s'',t'') (r',s',t'):  r'' = s''*a + t''*b and r' = s'*a + t'*b 
  eval u             (0 ,_ ,_ ) = u
  eval (r'',s'',t'') (r',s',t') 
    = s' `seq` t' `seq` eval (r',s',t') (r,s'' - q*s',t'' - q*t') where (q,r) = divMod r'' r'

--------------------------------------------------------------------------------
-- gcd -

-- | greatest common divisor.
--
-- __Properties__ For all @a@ and @b@ in 'N' holds:
--
-- (1) @gcd a b '==' gcd b a@.
--
-- (2) @gcd a b '==' 0@ if and only if @a '==' 0@ and @b '==' 0@.
--
-- (4) @gcd a 0 '==' a@.
--
-- (4) @gcd a 1 '==' 1@.
--
-- (5) @gcd a b '*' 'lcm' a b '==' a '*' b@.
gcd :: N -> N -> N
gcd a b = g where (g,_,_) = euclid (inj a) (inj b)

--------------------------------------------------------------------------------
-- gcds -

-- | greatest common divisor of the given list.
--
-- __Note__ @gcds [] '==' 0@.
gcds :: [N] -> N
gcds = foldl gcd 0

--------------------------------------------------------------------------------
-- lcm -

-- | least common multiple.
--
-- __Properties__ For all @a@ and @b@ in 'N' holds:
--
-- (1) @lcm a b '==' lcm b a@.
--
-- (2) @lcm a b '==' 1@ if and only if @a '==' 1@ and @b '==' 1@.
--
-- (3) @lcm a 0 '==' 0@.
--
-- (4) @lcm a 1 '==' a@.
--
-- (5) @'gcd' a b '*' lcm a b '==' a '*' b@.
lcm :: N -> N -> N
lcm 0 0 = 0
lcm a b = (a * b) `div` gcd a b

--------------------------------------------------------------------------------
-- lcms -

-- | least common multiple of the given list.
--
-- __Property__ @'lcms' [] '==' 1@.
lcms :: [N] -> N
lcms = foldl lcm 1
