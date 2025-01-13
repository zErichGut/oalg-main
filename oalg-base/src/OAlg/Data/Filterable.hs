
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      : OAlg.Data.Filterable
-- Description : filtrations.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- filtrations.
module OAlg.Data.Filterable
  (  Filterable(..)
  )
  where

import qualified Data.List as L

--------------------------------------------------------------------------------
-- Filterable -

-- | filtering.
class Filterable s x where
  filter :: (x -> Bool) -> s x -> s x

instance Filterable [] x where
  filter = L.filter
