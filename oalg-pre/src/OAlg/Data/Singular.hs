
-- |
-- Module      : OAlg.Data.Singular
-- Description : singular types
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- parameterized types with at most on constructor.
module OAlg.Data.Singular
  ( Singular, (<==>)
  )
  where

import Data.Proxy

import OAlg.Data.Equal
import OAlg.Control.Exception

--------------------------------------------------------------------------------
-- Singular -

-- | parameterized types with at most on constructor.
--
-- __Definition__ A type function @__p__@ is called __/singular/__ if and only if for each type @__x__@
-- there is at most one constructor for @__p__ __x__@.
class Eq1 p => Singular p where


instance Singular Proxy 

--------------------------------------------------------------------------------
-- (<==>) -

-- | equivalence of witnesses in @__p__ __x__@.
--
-- __Note__ @p '<==>' q@ returns either 'True' or an 'ImplementationError' will
-- be thrown.
(<==>) :: Singular p => p x -> p x -> Bool 
p <==> q = if eq1 p q
             then True
             else throw (ImplementationError "singular type with different values")



