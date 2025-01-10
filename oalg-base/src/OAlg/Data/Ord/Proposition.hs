
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}

-- |
-- Module      : OAlg.Data.Ord.Proposition
-- Description : propositions on ordered structures and lattices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- propositions on ordered structures and lattices.
module OAlg.Data.Ord.Proposition
  ( -- * Lattice
    prpLattice, prpLatticeDisjunction, prpLatticeConjunction

    -- * Erasable Lattice
  , prpErasableLattice

    -- * Bool
  , prpOrdBool

    -- * Ord
  , prpOrd
  )
  where

import OAlg.Data.Ord.Definition
import OAlg.Data.Opposite
import OAlg.Data.Show
import OAlg.Data.Boolean.Definition
import OAlg.Data.Statement.Definition
import OAlg.Data.X

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
-- prpOrdBool -

-- | validity of 'Bool as a erasable lattice
prpOrdBool :: Statement
prpOrdBool = Prp "OrdBool" :<=>:
  And [ prpLattice xBool
      , prpErasableLattice xBool
      ]

--------------------------------------------------------------------------------
-- prpOrd -

-- | propositions for ordered structures and lattices.
prpOrd :: Statement
prpOrd = Prp "Ord" :<=>:
  And [ prpOrdBool
      ]
