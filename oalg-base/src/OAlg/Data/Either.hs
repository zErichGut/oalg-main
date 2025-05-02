
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
    Either(..), either

    -- * Either1
  , Either1(..), either1
  
    -- * Either2
  , Either2(..)
  )
  where 

import OAlg.Data.Show
import OAlg.Data.Equal

--------------------------------------------------------------------------------
-- Either1 -

-- | disjoint union of two 1-parameterized data types.
data Either1 f g x where
  Left1  :: f x -> Either1 f g x
  Right1 :: g x -> Either1 f g x

instance (Show1 f, Show1 g) => Show1 (Either1 f g) where
  show1 (Left1 f)  = "Left11 (" ++ show1 f ++ ")"
  show1 (Right1 g) = "Right1 (" ++ show1 g ++ ")"

instance (Show1 f, Show1 g) => Show (Either1 f g x) where
  show = show1

instance (Eq1 f, Eq1 g) => Eq1 (Either1 f g) where
  eq1 (Left1 x) (Left1 y)   = eq1 x y
  eq1 (Right1 x) (Right1 y) = eq1 x y
  eq1 _ _                   = False

instance (Eq1 f, Eq1 g) => Eq (Either1 f g x) where
  (==) = eq1

--------------------------------------------------------------------------------
-- either1 -

-- | the induced map.
either1 :: (f x -> y) -> (g x -> y) -> Either1 f g x -> y
either1 f _ (Left1 fx)  = f fx
either1 _ g (Right1 gx) = g gx

--------------------------------------------------------------------------------
-- Either2 -

-- | disjoint union of two 2-parameterized data types.
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

instance (Eq2 f, Eq2 g) => Eq (Either2 f g x y) where
  (==) = eq2
