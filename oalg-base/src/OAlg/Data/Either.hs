
{-# LANGUAGE GADTs #-}

-- |
-- Module      : OAlg.Data.Either
-- Description : disjoint union of data
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- disjoint union of data.
module OAlg.Data.Either
  ( -- * Either
    Either(..)

    -- * Either2
  , Either2(..)
  )
  where 

import OAlg.Data.Show
import OAlg.Data.Equal

--------------------------------------------------------------------------------
-- Either2 -

-- | disjoint union of two parameterized data types.
data Either2 f g a b where
  Left2 :: f a b -> Either2 f g a b
  Right2 :: g a b -> Either2 f g a b

--------------------------------------------------------------------------------
-- Either2 -
instance (Show2 f, Show2 g) => Show2 (Either2 f g) where
  show2 (Left2 f)  = "Left2 (" ++ show2 f ++ ")"
  show2 (Right2 g) = "Right2 (" ++ show2 g ++ ")"

instance (Show2 f, Show2 g) => Show (Either2 f g x y) where
  show = show2
  
instance (Eq2 f, Eq2 g) => Eq2 (Either2 f g) where
  eq2 (Left2 f) (Left2 g)   = eq2 f g
  eq2 (Right2 f) (Right2 g) = eq2 f g
  eq2 _ _                   = False

