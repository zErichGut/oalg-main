
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}


-- |
-- Module      : OAlg.Data.Boolean.Definition
-- Description : definition of boolean structures
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- boolean structure for multivalent logic. 
module OAlg.Data.Boolean.Definition
  ( -- * Logical Operators
    Logical(..), Erasable(..)
    
    -- * Boolean
  , Boolean(..)

    -- * Bool
  , B.Bool(..), B.otherwise

    -- * Structure
  -- , Bol
  )
  where

import Prelude as P hiding (not,(||),(&&),or,and)
import qualified Data.Bool as B

import OAlg.Data.Opposite

--------------------------------------------------------------------------------
-- Lagical -

-- | logical structures admitting a general definition for /disjunctions/ and /conjunctions/.
class Logical a where
  infixr 2 ||
  -- | disjunction
  (||) :: a -> a -> a
  
  infixr 3 &&  
  -- | conjunction
  (&&) :: a -> a -> a

instance Logical Bool where
  (||)  = (B.||)
  (&&)  = (B.&&)

instance Logical a => Logical (Op a) where
  Op a || Op b = Op (a && b)
  Op a && Op b = Op (a || b)

--------------------------------------------------------------------------------
-- Erasable -

-- | erasor-operator.
class Erasable a where
  infixl 4 //
  -- | difference
  (//) :: a -> a -> a
  default (//) :: Boolean a => a -> a -> a
  a // b = a && not b

instance Erasable Bool

instance Eq x => Erasable [x] where
  xs // [] = xs
  [] // _  = []
  (x:xs) // (y:ys) = case x == y of
    True  -> xs // ys
    False -> x : (xs // (y:ys))

--------------------------------------------------------------------------------
-- Boolean -

infixr 1 ~>, <~>

-- | types with a 'Boolean' structure, allowing multivalent logic.
--
--   __Note__ Every 'Enum' type which is also 'Bounded' has a natural implementation
--   as @'false' = 'minBound'@, @'true' = 'maxBound'@, @('||') = 'max'@, @('&&') = 'min'@
--   (as there are min and max bounds the operator ('||') and @('&&')@ should be
--    implemented with a lazy variant of 'min' and 'max') and
--    @'not' b = 'toEnum' ('fromEnum' 'maxBound' '-' 'fromEnum' t)@.
class Logical b => Boolean b where
  {-# MINIMAL true, false, not #-}
  false :: b 
  true  :: b

  not   :: b -> b
  
  or    :: [b] -> b
  or []     = false
  or (a:as) = a || or as
  
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
  (<~>) = (==)
