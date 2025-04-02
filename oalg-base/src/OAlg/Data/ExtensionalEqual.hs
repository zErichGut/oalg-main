
-- |
-- Module      : OAlg.Data.ExtensionalEqual
-- Description : extensional equality for functions.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- extensional equality for functions.
module OAlg.Data.ExtensionalEqual
  ((.=.), prpExtensionalEqual)
  where

import OAlg.Data.X
import OAlg.Data.Statement
import OAlg.Data.Validable

--------------------------------------------------------------------------------
-- prpExtensionalEqual -

-- | validity for two functions being __/extensional equal/__, i.e. for all @f@ and @g@ in
-- @__x__ -> __y__@ and @x@ in @__x__@ holds: @f x '==' g y@.
prpExtensionalEqual :: (Show x, Eq y) => X x -> (x -> y) -> (x -> y) -> Statement
prpExtensionalEqual xx f g = Prp "ExtensionalEqual" :<=>: Forall xx
  (\x -> (f x == g x) :?> Params ["x":=show x]
  )

--------------------------------------------------------------------------------
-- (.=.) -

infix 4 .=.
-- | extensional equality for two functions.
--
-- __Note__ We use this notation even if the constraints 'XStandard' dos not hold.
(.=.) :: (Show x, Eq y, XStandard x) => (x -> y) -> (x -> y) -> Statement
(.=.) = prpExtensionalEqual xStandard

