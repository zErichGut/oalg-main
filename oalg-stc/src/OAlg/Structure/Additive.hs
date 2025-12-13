
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Structure.Additive
-- Description : additive structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- 'Additive' structures.
module OAlg.Structure.Additive
  ( module Add
  , module Prp
  )
  where

import OAlg.Structure.Additive.Definition as Add
import OAlg.Structure.Additive.Proposition as Prp
