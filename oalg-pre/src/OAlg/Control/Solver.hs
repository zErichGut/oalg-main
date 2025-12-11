
{-# LANGUAGE ExistentialQuantification, StandaloneDeriving, ScopedTypeVariables #-}

-- |
-- Module      : OAlg.Control.Solver
-- Description : solver with possible failure
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- A monad to express solving algebraic problems which may fail.
--
-- __Note__ To express algebraic unsolvable
--  - e.g determine the multiplicative inverse of 0 - one should only
--  use the @'failure'@ mechanism from this module (see examples in @'solvable'@).
module OAlg.Control.Solver
  ( -- * Result Type For Solving Algebraic Problems
    Solver(), failure, handle, solve, solvable
  )
  where

import Control.Exception hiding (handle)

--------------------------------------------------------------------------------
-- Solver

-- | monad to solve algebraic problems which may fail because it is not solvable or ...
data Solver x
  = Solution x
  | forall e . Exception e => Failure e

deriving instance Show x => Show (Solver x)

instance Functor Solver where
  fmap f (Solution x) = Solution (f x)
  fmap _ (Failure e)  = Failure e

instance Applicative Solver where
  pure = Solution
  (Solution f) <*> (Solution x) = Solution (f x)
  (Failure e)  <*> _            = Failure e
  _            <*> (Failure e)  = Failure e     

instance Monad Solver where
  return = pure
  (Solution x) >>= f = f x
  (Failure e)  >>= _ = Failure e

-- | extracting the solution from the solver. If during solving an exception @e@ occurs, then @e@ will
-- be thrown via the regular @throw@ mechanism of @'Control.Exception'@.
--
-- __Note__ @solve@ extracts the solution lazy!
solve :: Solver x -> x
solve (Solution x) = x 
solve (Failure e)  = throw e

-- | checks for solvability of a algebraic problem represented be a solver @s@ (see also @'solve'@). 
solvable :: Solver r -> Bool
solvable (Solution _) = True
solvable (Failure _)  = False

-- | throwing exception in to @'Solver'@ to express unsolvable.
failure :: Exception e => e -> Solver x
failure = Failure

-- | handling exception.
--
-- __Note__ Only exceptions expressed via the @'failure'@ mechanism can be handled by 'handle'!
handle :: Exception e => Solver x -> (e -> Solver x) -> Solver x
handle x@(Solution _) _ = x
handle f@(Failure e)  h = case fromException $ toException $ e of
                              Just e' -> h e'
                              _       -> f
