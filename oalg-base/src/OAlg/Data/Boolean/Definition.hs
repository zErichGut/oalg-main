
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE  MultiParamTypeClasses #-}


-- |
-- Module      : OAlg.Data.Boolean.Definition
-- Description : definition of boolean structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- boolean structure for multivalent logic. 
module OAlg.Data.Boolean.Definition
  (
    -- * Boolean
    Boolean(..)

    -- * Bool
  , B.Bool(..), B.otherwise

    -- * Structure
  , Bol
  )
  where

import Prelude as P hiding (not,(||),(&&),or,and)
import qualified Data.Bool as B
import OAlg.Structure.Definition

--------------------------------------------------------------------------------
-- Boolean -

infixr 3 &&
infixr 2 ||
infixr 1 ~>, <~>

-- | types with a 'Boolean' structure, allowing multivalent logic.
--
--   __Note__ Every 'Enum' type which is also 'Bounded' has a natural implementation
--   as @'false' = 'minBound'@, @'true' = 'maxBound'@, @('||') = 'max'@, @('&&') = 'min'@
--   (as there are min and max bounds the operator ('||') and @('&&')@ should be
--    implemented with a lazy variant of 'min' and 'max') and
--    @'not' b = 'toEnum' ('fromEnum' 'maxBound' '-' 'fromEnum' t)@.
class Boolean b where
  {-# MINIMAL true, false, not, ((||), (&&) | or, and) #-}
  false :: b 
  true  :: b

  not   :: b -> b
  
  (||)  :: b -> b -> b
  a || b = or [a,b]
  
  or    :: [b] -> b
  or []     = false
  or (a:as) = a || or as
  
  (&&)  :: b -> b -> b
  a && b = and [a,b]
  
  and   :: [b] -> b
  and []     = true
  and (a:as) = a && and as

  
  (~>) :: b -> b -> b
  a ~> b = not a || b

  (<~>) :: b -> b -> b
  a <~> b = (a ~> b) && (b ~> a)

  eqvl   :: [b] -> b
  eqvl []     = true
  eqvl (a:as) = and impls where
    impls = map (uncurry (~>)) (zip (a:as) (as++[a]))

instance Boolean Bool where
  false = False  
  true  = True
  not   = B.not
  (||)  = (B.||)
  (&&)  = (B.&&)
  (<~>) = (==)

--------------------------------------------------------------------------------
-- Bol -

-- | type representing 'Boolean' structures.
data Bol

type instance Structure Bol x = Boolean x

