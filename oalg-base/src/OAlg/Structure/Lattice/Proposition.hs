
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Structure.Lattice.Proposition
-- Description : propositions on lattices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on lattices.
module OAlg.Structure.Lattice.Proposition
  ( -- * Lattice
    prpLattice, prpLatticeDisjunction, prpLatticeConjunction

    -- * Erasable Lattice
  , prpErasableLattice

    -- * Bool
  , prpLatticeBool

  )
  where

import OAlg.Prelude

import OAlg.Data.POrd

import OAlg.Structure.Lattice.Definition

--------------------------------------------------------------------------------
-- prpLatticeDisjunction -

-- | validity of disjunction in a lattice.
prpLatticeDisjunction :: (Lattice a, Show a) => a -> a -> a -> Statement
prpLatticeDisjunction a b c = Label "LatticeDisjunction" :<=>:
  And [ Label "a <<= (a || b)"
          :<=>: (a <<= ab) :?> Params ["a":=show a,"b":=show b]
      , Label "b <<= (a || b)"
          :<=>: (b <<= ab) :?> Params ["a":=show a,"b":=show b]
      , Label "(a <<= z) && (b <<= z) ~> (a || b) <<= z"
        :<=>:     (((a <<= z) && (b <<= z)) :?> Params ["a":=show a,"b":=show b,"z":=show z])
              :=> (ab <<= z) :?> Params ["a":=show a,"b":=show b,"z":=show z]
      ]
  where ab = a || b
        z  = ab || c

--------------------------------------------------------------------------------
-- prpLatticeConjunction -

-- | validity of conjunction in a lattice.
prpLatticeConjunction :: (Lattice a, Show a) => a -> a -> a -> Statement
prpLatticeConjunction a b c = Label "LatticeConjunction" :<=>:
  prpLatticeDisjunction (Op a) (Op b) (Op c)

--------------------------------------------------------------------------------
-- prpLattice -

-- | validity of a lattice.
prpLattice :: (Lattice a,Show a) => X a -> Statement
prpLattice xa = Prp "Lattice" :<=>:
  And [ Forall xaaa
          (\(a,b,c) -> And [ prpLatticeDisjunction a b c
                           , prpLatticeConjunction a b c
                           ]
          )
      ]
  where xaaa = xTupple3 xa xa xa

--------------------------------------------------------------------------------
-- prpErasableLattice -

-- | validity of a erasable lattice.
prpErasableLattice :: (ErasableLattice a, Show a) => X a -> Statement
prpErasableLattice xa = Prp "ErasableLattice" :<=>:
  And [ Forall xaa (\(a,b) -> ((a // b) <<= a) :?> Params ["a":=show a,"b":=show b])
      ]
  where xaa = xTupple2 xa xa

--------------------------------------------------------------------------------
-- prpLatticeBool -

-- | validity of 'Bool as a erasable lattice
prpLatticeBool :: Statement
prpLatticeBool = Prp "LatticeBool" :<=>:
  And [ prpLattice xBool
      , prpErasableLattice xBool
      ]

