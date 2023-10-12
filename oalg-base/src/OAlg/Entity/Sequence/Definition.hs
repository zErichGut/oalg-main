
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.Entity.Sequence.Definition
-- Description : basic definitions for sequences as mappings of an index to an entity
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- basic definitions for sequences as mappings of an index to an entity.
module OAlg.Entity.Sequence.Definition
  ( -- * Sequence
    Sequence(..), listN, (?), isEmpty, span, support, image

    -- * Constructable
  , ConstructableSequence(..)
  , sqcIndexMap

    -- * Exception
  , SequenceException(..)
  ) where

import Data.Proxy
import Data.List (head,zip,sort,group,map,filter)

import OAlg.Prelude
import OAlg.Structure.Ring
import OAlg.Structure.Number

import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Graph

--------------------------------------------------------------------------------
-- SequenceException -

-- | sequence exceptions which are sub exceptions from 'SomeOAlgException'.
data SequenceException
  = IndexOutOfSupport
  deriving (Eq,Show)

instance Exception SequenceException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Sequence -

-- | sequences as mappings of an index.
--
--  __Definition__ Let @__s__@, @__i__@, @__x__@ be an instance of 'Sequence' and @xs@ be
--  in @__s__ __x__@, then we call @xs@ __/finite/__ if and only if the evaluation of
--  @'lengthN' xs@ terminates and will not end up in an exception.
--
--  __Property__ Let @__s__@, @__i__@, @__x__@ be an instance of 'Sequence', then holds:
--
-- (1) For all @xs@ in @__s__ __x__@ holds:
--
--     (1) 'graph' is constant in its first parameter.
--
--     (2) If @xs@ is finite, then @'lengthN' xs '==' 'lengthN' ('graph' p xs)@ for any
--     @p@.
--
-- (2) For all @xs@ in @__s__ __x__@ holds:
--
--     (1) 'list' is constant in its first parameter.
--
--     (2) For all @..(x,i)':'(x,j)..@ in @xs@ holds: @i '<' j@.
--
--     (3) If @xs@ is finite, then @'lengthN' xs '==' 'lengthN' ('list' p xs)@ for any
--     @p@.
--
-- (3) Let @xs@ be in @__s__ __x__@ and @i@ in @__i__@, then holds:
-- there exists an @x@ in @__x__@ with @xs '?' i@ matches @'Just' x@ if and only if there
-- exists an @(i',x)@ in @'graph' (Just i) xs@ such that @i '==' i'@.
--
-- __Note__ The first parameter of 'graph' - respectively 'list' - serves only as a /proxy/
-- and as such it is only relevant on the type level.
class (LengthN (s x), Ord i) => Sequence s i x where
  {-# MINIMAL graph | list #-}

  -- | the associated graph of a sequence
  graph :: p i -> s x -> Graph i x
  graph p xs = Graph $ map (\(x,i) -> (i,x)) $ list p xs

  -- | the associated list of its items together with there index.
  list :: p i -> s x -> [(x,i)]
  list p xs = map (\(i,x) -> (x,i)) xs' where Graph xs' = graph p xs

  -- | the @i@-th item.
  (??) :: s x -> i -> Maybe x
  xs ?? i = gphLookup (graph (Just i) xs) i

--------------------------------------------------------------------------------
-- listN -

-- | the indexed list of the sequence.
listN :: Sequence s N x => s x -> [(x,N)]
listN = list (Proxy :: Proxy N)

--------------------------------------------------------------------------------
-- ConstructableSequence -

-- | constructable sequences.
class (Entity x, Entity i, Sequence s i x) => ConstructableSequence s i x where

  -- | constructs a sequence.
  sequence :: (i -> Maybe x) -> Set i -> s x

  infixl 7 <&
  -- | restricts a sequence.
  (<&) :: s x -> Set i -> s x
  (<&) xs is = sequence (xs??) is

--------------------------------------------------------------------------------
-- sqcIndexmap -

-- | mapping the indices according to the given set.
sqcIndexMap :: (ConstructableSequence s i x, Sequence s j x)
  => Set i -> (i -> j) -> s x -> s x
sqcIndexMap is f xjs = sequence ((xjs??).f) is


--------------------------------------------------------------------------------
-- isEmpty -

-- | checks for being empty.
isEmpty :: Sequence s i x => p i -> s x -> Bool
isEmpty p xs = case list p xs of
  [] -> True
  _  -> False

--------------------------------------------------------------------------------
-- (?) -

-- | the @i@-th element of the sequence.
--
--  __Property__ Let @xs@ be in @__s__ __x__@ and @i@ in @__i__@ for a instance of
--  @'Sequence' __s__ __i__ __x__@, then holds: If @i@ is in the 'support' of @xs@ then
--  @xs '?' i@ is the @i@-th item of @xs@, else its evaluation will end up by throwing a
--  'IndexOutOfSupport'-exception.
(?) :: Sequence s i x => s x -> i -> x
xs ? i = case xs ?? i of
  Just x -> x
  Nothing -> throw IndexOutOfSupport
  
--------------------------------------------------------------------------------
-- support -

-- | the support of a sequence, i.e. all the indices which are not mapped to 'Nothing'.
support :: Sequence s i x => p i -> s x -> Set i
support p xs = Set $ map fst $ gphxs $ graph p xs

--------------------------------------------------------------------------------
-- span -

-- | the span of a sequence.
span :: Sequence s i x => p i -> s x -> Span i
span p = setSpan . support p 

--------------------------------------------------------------------------------
-- image -

-- | the image of a sequence, i.e. all the entities are hit by the mapping.
image :: (Sequence s i x, Ord x) => p i -> s x -> Set x
image p xs = Set $ map head $ group $ sort $ map snd $ gphxs $ graph p xs

--------------------------------------------------------------------------------
-- [] - Sequence -

instance (Integral r, Enum r) => Sequence [] r x where
  graph _ xs = Graph ([rZero..] `zip` xs)

--------------------------------------------------------------------------------
-- lstSqc -

-- | @'lstSqc' f is@ maps the index set @is@ according to @f@ and strips out all 'Nothing'
--   items.
lstSqc :: (i -> Maybe x) -> Set i -> [x]
lstSqc mx (Set is)
  = map fromJust
  $ filter isJust
  $ map mx is

--------------------------------------------------------------------------------
-- [] - ConstructableSequence -

instance (Integral r, Enum r, Entity x) => ConstructableSequence [] r x where
  sequence = lstSqc

--------------------------------------------------------------------------------
-- Set - ConstructableSequence -

instance (Integral r, Enum r) => Sequence Set r x where
  list _ (Set xs) = xs `zip` [rZero .. ]
  
instance (Integral r, Enum r, Entity x, Ord x) => ConstructableSequence Set r x where
  sequence = setSqc

--------------------------------------------------------------------------------
-- Graph - ConstructableSequence -

instance Ord i => Sequence (Graph i) i x where
  graph _ = id

instance (Entity x, Entity i, Ord i) => ConstructableSequence (Graph i) i x where
  sequence = gphSqc

