
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Structure.Fibred.Proposition
-- Description : propositions on fibred structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on 'Fibred' structures.
module OAlg.Structure.Fibred.Proposition
  (
    -- * Fibred
    prpFbr
  )
  where

import OAlg.Prelude

import OAlg.Structure.Fibred.Definition

--------------------------------------------------------------------------------
-- prpFbr -

-- | validity for 'Fibred' structures.
prpFbr :: Fibred f => XFbr f -> Statement
prpFbr xs = Prp "Fbr"
  :<=>: Forall xs (\s -> valid s ~> valid (root s))


