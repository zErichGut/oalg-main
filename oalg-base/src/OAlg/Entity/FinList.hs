
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TupleSections #-}

{-# LANGUAGE NoStarIsType #-}

-- |
-- Module      : OAlg.Entity.FinList
-- Description : finite lists, parameterized by there length.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- finite lists, parameterized by there length.
module OAlg.Entity.FinList
  (
    -- * FinList
    FinList(..), toW, head, tail, zip, zip3, (|:), (++), (**), repeat
  , iFinList, iFinList0, iFinList', toArray

  , maybeFinList
  , someFinList, SomeFinList(..)
  , (<++>)

    -- ** Induction
  , inductionS, FinList'(..)
  )

  where

import Control.Monad as M

import Data.Typeable
import Data.Foldable
import Data.Array as A
import qualified Data.List as L

import OAlg.Prelude

import OAlg.Entity.Natural hiding ((++),(**))

--------------------------------------------------------------------------------
-- FinList - 
infixr 5 :|

-- | finite lists, parameterized by there length.
data FinList (n :: N') a where
  Nil  :: FinList N0 a
  (:|) :: a -> FinList n a -> FinList (n+1) a

----------------------------------------
-- FinList - Entity -
deriving instance Eq a => Eq (FinList n a)
deriving instance Foldable (FinList n)
deriving instance Typeable (FinList n a)
deriving instance Ord x => Ord (FinList n x)

instance Show a => Show (FinList n a) where
  show xs = "[|" L.++ (join $ tween "," $ amap1 show $ toList xs) L.++ "|]"

instance Applicative1 (->) (FinList n) where
  amap1 _ Nil     = Nil
  amap1 f (a:|as) = f a :| amap1 f as

instance Validable a => Validable (FinList n a) where
  valid as = vld 0 as where
    vld :: Validable a => N -> FinList n a -> Statement
    vld _ Nil = SValid
    vld i (a:|as) = (Label (show i) :<=>: valid a) && vld (succ i) as

instance (Typeable n, Entity a) => Entity (FinList n a)

--------------------------------------------------------------------------------
-- toW -

-- | the underlying witness.
toW :: FinList n a -> W n
toW Nil     = W0
toW (_:|as) = SW (toW as) 

--------------------------------------------------------------------------------
-- head -

-- | the head of a non empty finite list.
head :: FinList (n+1) a -> a
head (a :| _) = a

-------------------------------------------------------------------------------
-- tail -

-- | the tail of a non empty finite list.
tail :: FinList (n+1) a -> FinList n a
tail (_ :| as) = as 

--------------------------------------------------------------------------------
-- induction-

-- | Wrapper to switch the parameters.
newtype FinList' a n = FinList' (FinList n a)

hypotheseS :: (FinList i a -> FinList (i+1) a) -> FinList' a i -> FinList' a (i+1)
hypotheseS hs (FinList' s) = FinList' (hs s)

-- | induction for sequences.
inductionS :: Any n
  -> FinList N0 a
  -> (forall i . FinList i a -> FinList (i+1) a)
  -> FinList n a
inductionS w s0 hs = sn where FinList' sn = induction w (FinList' s0) (hypotheseS hs)   

--------------------------------------------------------------------------------
-- zip -

-- | zips two sequences of the same length.
zip :: FinList n a -> FinList n b -> FinList n (a,b)
zip Nil Nil = Nil
zip (a:|as) (b:|bs) = (a,b):|zip as bs

-- | zips three sequences of the same length. 
zip3 :: FinList n a -> FinList n b -> FinList n c -> FinList n (a,b,c)
zip3 as bs cs = amap1 (\((a,b),c) -> (a,b,c)) ((as `zip` bs) `zip` cs)

--------------------------------------------------------------------------------
-- (|:) -

infixl 5 |:
-- | appending an element at the end of the finite list.
(|:) :: FinList n a -> a -> FinList (n+1) a
Nil |: b     = b :| Nil
(a:|as) |: b = a :| (as|:b)

--------------------------------------------------------------------------------
-- (++) -

infixr 5 ++

-- | appending two finite lists.
(++) :: FinList n a -> FinList m a -> FinList (n+m) a
Nil ++ bs     = bs
(a:|as) ++ bs = a :| (as ++ bs)

--------------------------------------------------------------------------------
-- (**) -

-- | the product of two finite lists.
(**) :: FinList n a -> FinList m b -> FinList (n * m) (a,b)
Nil ** _ = Nil
(a :| as) ** bs = amap1 (a,) bs ++ (as ** bs)

--------------------------------------------------------------------------------
-- repeat -

-- | the constant sequence.
repeat :: Any n ->  a -> FinList n a
repeat n a = inductionS n Nil (a:|)

--------------------------------------------------------------------------------
-- toArray -

-- | maps a sequnece @as = a0..a(n-1)@ of length @n@ to the corresponding array @a@ with @ai '==' a'$'i@ for @i = 0..(n-1)@.
toArray :: FinList n a -> Array N a
toArray as = array b (L.zip [0..] as') where
  as' = toList as
  n   = lengthN as'
  b   = if 0 < n then (0,n>-1) else (1,0)

--------------------------------------------------------------------------------
-- iFinList -

-- | indexing finite lists, starting at the given natural number.
iFinList :: N -> FinList n a -> FinList n (a,N)
iFinList _ Nil      = Nil
iFinList n (a:|as)  = (a,n):|iFinList (succ n) as   

-- | adjoins to each element its index, starting from '0'.
iFinList0 :: FinList n a -> FinList n (a,N)
iFinList0 = iFinList 0

-- | the sequence 0,1 .. n-1.
iFinList' :: Any n -> FinList n N
iFinList' i = adj 0 i where
  adj :: N -> W n -> FinList n N
  adj _ W0      = Nil
  adj i (SW i') = i :| adj (succ i) i' 

--------------------------------------------------------------------------------
-- SomeFinList -

-- | some finite list.
data SomeFinList a = forall n . SomeFinList (FinList n a)

deriving instance Show a => Show (SomeFinList a)

instance Validable a => Validable (SomeFinList a) where
  valid (SomeFinList xs) = valid xs

instance Applicative1 (->) SomeFinList where
  amap1 f (SomeFinList xs) = SomeFinList (amap1 f xs)
  

--------------------------------------------------------------------------------
-- someFinList -

-- | the associated finite list.
someFinList :: [a] -> SomeFinList a
someFinList [] = SomeFinList Nil
someFinList (a:as) = case someFinList as of
  SomeFinList as' -> SomeFinList (a:|as')

--------------------------------------------------------------------------------
-- maybeFinList -

maybeFinList :: Any n -> [a] -> Maybe (FinList n a)
maybeFinList W0 _          = Just (Nil)
maybeFinList _ []          = Nothing
maybeFinList (SW n) (a:as) = maybeFinList n as >>= return . (a:|)

--------------------------------------------------------------------------------
-- (<++>) -

infixr 5 <++>
-- | concatenation.
(<++>) :: SomeFinList x -> SomeFinList x -> SomeFinList x
SomeFinList xs <++> SomeFinList ys = SomeFinList (xs ++ ys)


{-
--------------------------------------------------------------------------------
-- iFoldl -

iFoldl :: (a -> b -> a) -> a -> FinList n b -> a
iFoldl _ a Nil       = a
iFoldl (*) a (b:|bs) = iFoldl (*) (a*b) bs 
-}
