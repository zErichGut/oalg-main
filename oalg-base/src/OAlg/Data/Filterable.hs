
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
class Filterable s where
  filter :: (x -> Bool) -> s x -> s x

instance Filterable [] where
  filter = L.filter
