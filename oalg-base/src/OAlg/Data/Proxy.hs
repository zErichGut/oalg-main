
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Data.Proxy
-- Description : proxies.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- proxies.
module OAlg.Data.Proxy
  ( module Prx

  , Proxy2(..), Proxy3(..)
  )
  where

import Data.Proxy as Prx

data Proxy2 a b = Proxy2 deriving (Read,Show,Eq,Ord)
data Proxy3 a b c = Proxy3 deriving (Read,Show,Eq,Ord) 
  

