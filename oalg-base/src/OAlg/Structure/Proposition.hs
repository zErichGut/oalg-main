
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Structure.Vectorial.Definition
-- Description : propositions on basic algebraic structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- propositions on basic algebraic structures.
module OAlg.Structure.Proposition
  ( -- * Proposition
    prpStructure
  , prpStructureN, prpStructureZ, prpStructureQ
  , prpStructureOS
  )

  where

import OAlg.Prelude


import OAlg.Structure.Lattice
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
import OAlg.Structure.Distributive

--------------------------------------------------------------------------------
-- prpStructureN -

-- | validity of the algebraic structure of 'N'.
prpStructureN :: Statement
prpStructureN = Prp "StructureN" :<=>:
  And [ prpOrt (xStandard :: XOrt N)
      , prpMlt (xStandardMlt :: XMlt N)
      , prpFbr (xStandard :: XFbr N)
      , prpFbrOrt (xStandard :: XFbrOrt N)
      , prpAdd (xStandardAdd :: XAdd N)
      , prpDst (xStandardDst :: XDst N)
      ]

--------------------------------------------------------------------------------
-- prpStructureZ -

-- | validity of the algebraic structure of 'Z'.
prpStructureZ :: Statement
prpStructureZ = Prp "StructureZ" :<=>:
  And [ prpOrt (xStandard :: XOrt Z)
      , prpMlt (xStandardMlt :: XMlt Z)
      , prpFbr (xStandard :: XFbr Z)
      , prpFbrOrt (xStandard :: XFbrOrt Z)
      , prpAdd (xStandardAdd :: XAdd Z)
      , prpDst (xStandardDst :: XDst Z)
      ]

--------------------------------------------------------------------------------
-- prpStructureQ -

-- | validity of the algebraic structure of 'Q'.
prpStructureQ :: Statement
prpStructureQ = Prp "StructureQ" :<=>:
  And [ prpOrt (xStandard :: XOrt Q)
      , prpMlt (xStandardMlt :: XMlt Q)
      , prpFbr (xStandard :: XFbr Q)
      , prpFbrOrt (xStandard :: XFbrOrt Q)
      , prpAdd (xStandardAdd :: XAdd Q)
      , prpDst (xStandardDst :: XDst Q)
      ]

--------------------------------------------------------------------------------
-- prpStructureOS -

-- | validity of the algebraic structure of 'OS'.
prpStructureOS :: Statement
prpStructureOS = Prp "StructureOS" :<=>:
  And [ prpOrt (xStandard :: XOrt OS)
      , prpMlt (xStandardMlt :: XMlt OS)
      , prpFbr (xStandard :: XFbr OS)
      , prpFbrOrt (xStandard :: XFbrOrt OS)
      , prpAdd (xStandardAdd :: XAdd OS)
      , prpDst (xStandardDst :: XDst OS)
      ]

--------------------------------------------------------------------------------
-- prpStructureOp -

prpStructureOp :: Statement
prpStructureOp = Prp "StructureOp" :<=>:
  And [ prpOrt (xStandard :: XOrt (Op OS))
      , prpMlt (xStandardMlt :: XMlt (Op OS))
      , prpFbr (xStandard :: XFbr (Op OS))
      , prpFbrOrt (xStandard :: XFbrOrt (Op OS))
      , prpAdd (xStandardAdd :: XAdd (Op OS))
      , prpDst (xStandardDst :: XDst (Op OS))
      ]

--------------------------------------------------------------------------------
-- prpStructureId -

prpStructureId :: Statement
prpStructureId = Prp "StructureId" :<=>:
  And [ prpOrt (xStandard :: XOrt (Id OS))
      , prpMlt (xStandardMlt :: XMlt (Id OS))
      , prpFbr (xStandard :: XFbr (Id OS))
      , prpFbrOrt (xStandard :: XFbrOrt (Id OS))
      , prpAdd (xStandardAdd :: XAdd (Id OS))
      , prpDst (xStandardDst :: XDst (Id OS))
      ]

--------------------------------------------------------------------------------
-- prpStructure -

-- | validity of some structures.
prpStructure :: Statement
prpStructure = Prp "Structure" :<=>:
  And [ prpLatticeBool
      , prpStructureN
      , prpStructureZ
      , prpStructureQ
      , prpStructureOS
      , prpStructureOp
      , prpStructureId
      ]
