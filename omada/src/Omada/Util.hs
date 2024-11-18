
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : Omada.Util
-- Description : utilities
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- utilities.
module Omada.Util
  ( tween
  ) where

tween :: a -> [a] -> [a]
tween _ []     = []
tween _ [a]    = [a]
tween d (a:as) = a : d : tween d as

