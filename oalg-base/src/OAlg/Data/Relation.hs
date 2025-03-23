
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.Dualisable
-- Description : binary relations.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- binary relations.
module OAlg.Data.Relation
  ( -- * Symmetric
    Symmetric(..)
  )
  where

--------------------------------------------------------------------------------
-- Symmetric -

-- | symmetric relation.
class Symmetric r where
  swap :: r x y -> r y x
  

