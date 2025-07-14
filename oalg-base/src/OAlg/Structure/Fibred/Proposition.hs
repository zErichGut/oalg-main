
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

    -- * Fibre Oriented
  , prpFbrOrt

  )
  where

import OAlg.Prelude

import OAlg.Structure.Oriented

import OAlg.Structure.Fibred.Definition
import OAlg.Structure.Fibred.Oriented

--------------------------------------------------------------------------------
-- prpFbr -

-- | validity for 'Fibred' structures.
prpFbr :: Fibred f => XFbr f -> Statement
prpFbr xs = Prp "Fbr"
  :<=>: Forall xs (\s -> valid s ~> valid (root s))

--------------------------------------------------------------------------------
-- prpFbrOrt -

-- | validity for 'FibredOriented' structures.
prpFbrOrt :: FibredOriented f => XFbrOrt f -> Statement
prpFbrOrt xs = Prp "FbrOrt" :<=>:
  Label "1" :<=>: root .=. orientation where (.=.) = prpEqualExt xs


