
-- | Symbols from 'A' to 'Z'. They are primarly used to validate the
--   algebraic structure of 'OAlg.Structure.Multiplicative.Orientation'.
module OAlg.Data.Symbol
  ( Symbol(..), xSymbol
  )
  where

import Control.DeepSeq(NFData(..))

import OAlg.Data.X
import OAlg.Data.Validable

--------------------------------------------------------------------------------
-- Symbol -

-- | Symbols from 'A' to 'Z'.
data Symbol
  = A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

instance NFData Symbol where
  rnf A = ()
  rnf _ = ()

instance Validable Symbol where
  valid = rnfValid

instance XStandard Symbol where
  xStandard = xSymbol
  
--------------------------------------------------------------------------------
-- xSymbol -

-- | uniformly distributed random variable of 'Symbol'.
xSymbol :: X Symbol
xSymbol = xEnum

