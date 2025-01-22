
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Structure.PartiallyOrdered.Proposition
-- Description : propositions on partially ordered types.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on partially ordered types.
module OAlg.Structure.PartiallyOrdered.Proposition
  (  prpErasable
  , prpSomePartiallyOrdered

  )
  where

import OAlg.Prelude

import OAlg.Data.Symbol

import OAlg.Structure.PartiallyOrdered.Definition



--------------------------------------------------------------------------------
-- prpErasable -

-- | validity of a erasable lattice.
prpErasable :: (PartiallyOrdered a, Erasable a, Show a) => X a -> Statement
prpErasable xa = Prp "ErasableLattice" :<=>:
  And [ Forall xaa (\(a,b) -> ((a // b) <<= a) :?> Params ["a":=show a,"b":=show b])
      ]
  where xaa = xTupple2 xa xa


--------------------------------------------------------------------------------
-- prpSomePartiallyOrdered -

-- | validity of some partially ordered types.
prpSomePartiallyOrdered :: Statement
prpSomePartiallyOrdered = Prp "LatticeBool" :<=>:
  And [ prpErasable xBool
      , prpErasable (xTakeB 0 20 (xStandard :: X Symbol))
      ]

