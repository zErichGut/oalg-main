
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module      : OAlg.Data.EqualExtensional
-- Description : extensional equality.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- extensional equality.
module OAlg.Data.EqualExtensional
  ( EqExt(..), prpEqualExt
  )
  where

import OAlg.Data.Show
import OAlg.Data.X
import OAlg.Data.Equal
import OAlg.Data.Statement.Definition

--------------------------------------------------------------------------------
-- EqExt -

infix 4 .=.

-- | extensional equality.
--
-- __Properties__ Let @'EqExt' __c__@ then for all @__x__@, @__y__@ holds:
--
-- (1) For all @f@ in @__c x y__@ holdst: @f '.=.' f@.
--
-- (2) For all @f@, @g@ in @__c x y__@ holdst: If @f '.=.' g@ then holds
-- @g '.=.' f@.
--
-- (3) For all @f@, @g@ and @h@ in @__c x y__@ holds: If @f '.=.' g@ and @g .=:' h@ then
-- @f '.=.' h@.
class EqExt c where
  (.=.) :: c x y -> c x y -> Statement
  default (.=.) :: Eq2 c => c x y -> c x y -> Statement
  f .=. g = eq2 f g :?> Params []

--------------------------------------------------------------------------------
-- prpEqualExt -

-- | validity for two functions being __/extensional equal/__, i.e. for all @f@ and @g@ in
-- @__x__ -> __y__@ and @x@ in @__x__@ holds: @f x '==' g y@.
prpEqualExt :: (Show x, Eq y) => X x -> (x -> y) -> (x -> y) -> Statement
prpEqualExt xx f g = Prp "ExtensionalEqual" :<=>: Forall xx
  (\x -> (f x == g x) :?> Params ["x":=show x]
  )

