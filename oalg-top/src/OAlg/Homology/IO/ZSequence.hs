
{-# LANGUAGE NoImplicitPrelude #-}

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
-- Module      : OAlg.Homology.IO.ZSequence
-- Description : maps
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 
module OAlg.Homology.IO.ZSequence
  ( ZSequence, zsqSequence, zsqSupport
  , module M
  ) where

import Control.Monad

import Data.Map.Lazy as M hiding (valid)

import OAlg.Prelude

instance (Validable k, Validable v) => Validable (Map k v) where
  valid m = Label "Map" :<=>: (valid $ assocs m)

--------------------------------------------------------------------------------
-- ZSequence -

type ZSequence = M.Map Z

--------------------------------------------------------------------------------
-- zsqSequence -

zsqSequence :: (Z -> x) -> ZSequence x -> Z -> x
zsqSequence df xs z = case z `lookup` xs of
  Just x  -> x
  Nothing -> df z 

--------------------------------------------------------------------------------
-- zsqSupport -

zsqSupport :: ZSequence x -> Maybe (Z,Z)
zsqSupport xs = do
  (l,_) <- lookupMin xs
  (h,_) <- lookupMax xs
  return (l,h)
