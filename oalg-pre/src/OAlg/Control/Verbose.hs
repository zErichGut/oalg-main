
{-# LANGUAGE FlexibleInstances #-}

-- |
-- Module      : OAlg.Control.Verbose
-- Description : verbosity on showing
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- verbosity on showing.
module OAlg.Control.Verbose
  (
    -- * Verbose
    Verbose(..), Verbosity(..)
  , vshowStr, mnString, vshowList, mnList

    -- * Percent
  , Percent(..), showPercent
  )
  where

import Control.Monad (join)

import OAlg.Data.Show

--------------------------------------------------------------------------------
-- Verbose -

-- | kinds of verbosity.
data Verbosity
  = Low | Middle | High | Full | Pretty deriving (Show,Eq,Ord,Enum,Bounded)

-- | shows @a@ in the context of verbosity.
class Show a => Verbose a where
  -- | the default implementation is: @vshow v a = vshowStr ('mnString' v) (show a)@
  vshow :: Verbosity -> a -> String
  vshow v a = vshowStr (mnString v) (show a)

{-
mmax :: Maybe Int -> Int -> Maybe Int
mmax ma b = ma >>= \i -> return (max b i)
-}

--------------------------------------------------------------------------------
-- vshowStr -

-- | default length for a string representation in context of verbosity.
mnString :: Verbosity -> Maybe Int
mnString Low    = Just 10
mnString Middle = Just 20
mnString High   = Just 40
mnString _      = Nothing

-- | verbosely showing a string by the given length.
--
-- __Example__
--
-- >>> vshowStr (Just 3) "123456789"
-- "123.."
--
-- >>> vshowStr Nothing "123456789"
-- "123456789"
vshowStr :: Maybe Int -> String -> String
vshowStr mi str = case mi of
    Just n  -> str' ++ dots r where (str',r) = splitAt n str
    Nothing -> str
  where dots [] = []
        dots _  = ".."

--------------------------------------------------------------------------------
-- vshowList -

-- | default number of entries for a list representation in context of verbosity.
mnList :: Verbosity -> Maybe Int
mnList Low    = Just 2
mnList Middle = Just 10
mnList High   = Just 100
mnList _      = Nothing

-- | verbosely showing a list by the given length.
--
-- __Examples__
--
-- >>> vshowList Full (Just 3) "[" "]" "abcdef"
-- "['a','b','c'..]"
--
-- >>> vshowList Low (Just 3) "{" "}" ["abcdef","ghijklmn","op","qrst","uvwxyz"]
-- "{['a','b'..],['g','h'..],['o','p']..}"
vshowList :: Verbose a 
          => Verbosity
          -> Maybe Int
          -> String -> String
          -> [a]
          -> String
vshowList v mn db de xs
  = db ++ vslst' mn xs ++ de
    where dots [] = ""
          dots _  = ".."
          
          vslst' mn' xs' = case mn' of
              Just n  -> (join $ tween "," $ ss') ++ dots r where (ss',r) = splitAt n ss
              Nothing -> join $ tween "," $ ss
            where ss = map (vshow v)  xs'

instance Verbose Char where
  vshow _ = show

mnIntegrals :: Verbosity -> Maybe Int
mnIntegrals Low    = Just 3
mnIntegrals Middle = Just 5
mnIntegrals High   = Just 7
mnIntegrals _      = Nothing

----------------------------------------
-- Some instances -

instance Verbose Int where
  vshow v n = vshowStr (mnIntegrals v) (show n)

instance Verbose Integer where
  vshow v n = vshowStr (mnIntegrals v) (show n)

instance Verbose a => Verbose [a] where
  vshow v = vshowList v (mnList v) "[" "]"

instance Verbose Double

----------------------------------------
-- Verbose - Tuple -

vshowTuple :: [String] -> String
vshowTuple ss = "(" ++ (join $ tween "," ss) ++ ")"

instance Verbose () where
  vshow _ _ = vshowTuple []

instance (Verbose a,Verbose b) => Verbose (a,b) where
  vshow v (a,b) = vshowTuple [vshow v a,vshow v b]

instance (Verbose a,Verbose b,Verbose c) => Verbose (a,b,c) where
  vshow v (a,b,c) = vshowTuple [vshow v a,vshow v b,vshow v c]

instance (Verbose a,Verbose b,Verbose c,Verbose d) => Verbose (a,b,c,d) where
  vshow v (a,b,c,d) = vshowTuple [vshow v a,vshow v b,vshow v c,vshow v d]

instance (Verbose a,Verbose b,Verbose c,Verbose d, Verbose e) => Verbose (a,b,c,d,e) where
  vshow v (a,b,c,d,e) = vshowTuple [vshow v a,vshow v b,vshow v c,vshow v d,vshow v e]

instance (Verbose a,Verbose b,Verbose c,Verbose d, Verbose e,Verbose f)
  => Verbose (a,b,c,d,e,f) where
  vshow v (a,b,c,d,e,f)
    = vshowTuple [vshow v a,vshow v b,vshow v c,vshow v d,vshow v e,vshow v f]


--------------------------------------------------------------------------------
-- Percent -

-- | tagging for showing percentage of a 'Double'.
newtype Percent x = Percent x deriving Show

nPercent :: Verbosity -> Int
nPercent Low    = 0
nPercent Middle = 2
nPercent _      = 4

instance Verbose (Percent Double) where
  vshow v (Percent x) = showPercent (nPercent v) x

--------------------------------------------------------------------------------
-- showPercent -

-- | showing a double as percent with the given precision.
--
-- __Example__
--
-- >>> showPercent 2 0.912837
-- " 91.28%"
showPercent :: Int -> Double -> String
showPercent n d = sprc ++ (if 0 < n then "." ++ sprm else "") ++ "%"
  where n'        = 10 ** toEnum n
        (prc,prm) = (properFraction :: Double -> (Integer,Double))
                    ((toEnum $ round $ (100 * n' * d)) / n')
        sprc'     = show prc
        sprc      = let dgs = length sprc' in (take (3 - dgs) $ repeat $ ' ') ++ sprc'

        sprm'     = (show :: Integer -> String) $ floor $ (n' * prm)
        sprm      = let dgs = length sprm' in sprm' ++ (take (n - dgs) $ repeat $ '0')
