
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Data.X
-- Description : random variables
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Random variables for stochastical validation.
module OAlg.Data.X
  (

    -- * Random Variable
    X(XEmpty), samples, getSamples, sample

    -- * Statistics
  , meanValue

    -- * Omega
  , Omega(), mkOmega, getOmega
    
    -- * X
  , xOmega
  , xInt, xIntB
  , xWord, xWordB
  , xInteger, xIntegerB
  , xChar, xCharB
  , xDouble, xDoubleB
  , xEnum, xEnumB, xBool
  , xTupple2, xTupple3
  , xTakeN, xTakeB, xList
  , xOneOf, xOneOfX, xOneOfW, xOneOfXW
  , xN, xNB, xZ, xZB, xQ
  
    -- * Tools
  , sum', putDistribution, putDistribution', putDistributionIO
  , putDstr, aspCnstr

    -- * Exception
  , XException(..)

  )
  where

import qualified System.Random as R

import Control.Monad
import Control.Applicative
import Control.Exception

import Data.Array

import OAlg.Control.Exception
import OAlg.Control.Action
import OAlg.Control.HNFData

import OAlg.Data.Canonical
import OAlg.Data.Statistics
import OAlg.Data.Number

--------------------------------------------------------------------------------
-- XException -

-- | Exceptions for random variables.
data XException
  = ProbablyEmpty String
  | IsEmpty
  deriving (Show)

instance Exception XException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Omega -

-- | A possible state of the /world/. It is used for @'run'@ or @'samples'@ to generate randomly
-- values.
data Omega = Omega R.StdGen deriving (Show)

instance Eq Omega where
  Omega g == Omega g' = show g == show g'

-- | makes a state.
mkOmega :: Int -> Omega
mkOmega i = Omega $ R.mkStdGen i

-- | gets randomly a state.
getOmega :: IO Omega
getOmega = R.getStdGen >>= (return . Omega)

--------------------------------------------------------------------------------
-- nMax -

-- | maximal number of iterations for 'xJoin'.
nMax :: Int
nMax = 20000

--------------------------------------------------------------------------------
-- X -

-- | random variable over __@x@__, possibly 'XEmpty'. Let __@x@__ be a type and
--   @xx@ in @'X' __x__@, then we use the idiom @x@ /__is in the range of__/
--   @xx@ if there exist a @o@ in 'Omega' such that @x@ is an element of
--   @'samples' xx o@.
--
--   __Note__
--
--   (1) For the empty set @O@ there is exactly one sigma algebra, i.e. the power
--   set of the empty set @O@, and for every set @X@ there is exactly one measurable
--   function @O -> X@, i.e. the empty function, and hence exactly one random variable
--   over @O@.
--
--   (1) To not run into non terminating programs, we restrict the implementation of
--   @xa '>>=' f@ to a maximal number of iterations to find a suitable sample in @xa@ for
--   which @f a@ is not empty. If the iterations exceed this maximum number, a 'ProbablyEmpty'
--   exception will be thrown.
data X x = X (Action Omega x) | XEmpty

instance HNFData (X x) where
  rhnf XEmpty = ()
  rhnf _      = ()

instance Functor X where
  fmap f (X xx) = X $ fmap f xx
  fmap _ XEmpty = XEmpty

instance Applicative X where
  pure = X . pure
  XEmpty <*> _ = XEmpty
  _ <*> XEmpty = XEmpty
  X f <*> X a  = X (f <*> a)

xJoinMax :: Int -> X (X a) -> X a
xJoinMax _ XEmpty = XEmpty
xJoinMax n (X axa) = X $ xj 0 axa where
  xj :: Int -> Action Omega (X a) -> Action Omega a
  xj i _ | n <= i = throw (ProbablyEmpty ("after " ++ show i ++ " iterations in xJoinMax"))
  xj i axa = do
    xa <- axa
    case xa of
      X a    -> a
      XEmpty -> xj (i+1) axa

xJoin :: X (X a) -> X a
xJoin = xJoinMax nMax
      
instance Monad X where
  return   = pure
  
  xa >>= f = xJoin (fmap f xa)

  (>>) = (*>)

instance MonadFail X where
  fail _ = XEmpty

--------------------------------------------------------------------------------
-- samples -

-- | infinite list of randomly picked samples of @xx@ according to a initial omega @o@. If
--   @xx@ is empty then the result will be @'[]'@.
samples :: X x -> Omega -> [x]
samples XEmpty _ = []
samples (X xx) o = smpls xx o where
  smpls xx o = let (x,o') = run xx o in x:smpls xx o'

--------------------------------------------------------------------------------
-- getSamples -

-- | gets a list of randomly picked samples.
getSamples :: N -- ^ length of the returned list
  -> X x -> IO [x]
getSamples n xx = getOmega >>= return . takeN n . samples xx

--------------------------------------------------------------------------------
-- sample -

-- | the first element of @'samples' xx o@. If @xx@ is empty then a 'IsEmpty' exception
--   will be thrown.
sample :: X x -> Omega -> x
sample xx o = case samples xx o of
  []  -> throw IsEmpty
  x:_ -> x

--------------------------------------------------------------------------------
-- xOmega

-- | random variable of 'Omega'.
xOmega :: X Omega
xOmega = X $ Action (\(Omega g) -> let (g1,g2) = R.split g in (Omega g1,Omega g2))

--------------------------------------------------------------------------------
-- xTupple2 -

-- | random variable for pairs.
xTupple2 :: X a -> X b -> X (a,b)
xTupple2 _ XEmpty = XEmpty
xTupple2 xa xb = do
  a <- xa
  b <- xb
  return (a,b)

--------------------------------------------------------------------------------
-- xTupple3 -

-- | random variable for triples.
xTupple3 :: X a -> X b -> X c -> X (a,b,c)
xTupple3 _ XEmpty _ = XEmpty
xTupple3 _ _ XEmpty = XEmpty
xTupple3 xa xb xc = do
  a <- xa
  b <- xb
  c <- xc
  return (a,b,c)

--------------------------------------------------------------------------------
-- xList -

-- | random variable of list.
xList :: [X x] -> X [x]
xList xxs = ucr xxs [] where
  ucr [] xs        = return xs
  ucr (XEmpty:_) _ = XEmpty
  ucr (xx:xxs) xs  = do
    x <- xx
    ucr xxs (x:xs)
    
--------------------------------------------------------------------------------
-- xTakeN -

-- | random variable of list with the given length for non empty random variables.
--   Otherwise the result will be 'XEmpty'.
xTakeN :: N -> X x -> X [x]
xTakeN _ XEmpty = XEmpty
xTakeN n xx = tk n [] where
  tk 0 xs = return xs
  tk n xs = xx >>= \x -> tk (pred n) (x:xs) 

--------------------------------------------------------------------------------
-- xTakeB -

-- | random variable of lists with a length between the given bounds.
xTakeB :: N -> N -> X x -> X [x]
xTakeB l h xx = xNB l h >>= \n -> xTakeN n xx

--------------------------------------------------------------------------------
-- X Int -

-- | uniformly distributed random variable of 'Int's.
xInt :: X Int
xInt = X $ Action (\(Omega g) -> let (i,g') = R.random g in (i,Omega g'))

-- | uniformly distributed random variable of 'Int's in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xIntB :: Int -> Int -> X Int
xIntB l h | h < l = XEmpty
xIntB l h = X $ Action (\(Omega g) -> let (i,g') = R.randomR (l,h) g in (i,Omega g'))

--------------------------------------------------------------------------------
-- X Word -

-- | uniformly distributed random variable of 'Word's.
xWord :: X Word
xWord = X $ Action (\(Omega g) -> let (i,g') = R.random g in (i,Omega g'))


-- | uniformly distributed random variable of 'Word's in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xWordB :: Word -> Word -> X Word
xWordB l h | h < l = XEmpty
xWordB l h = X $ Action (\(Omega g) -> let (i,g') = R.randomR (l,h) g in (i,Omega g'))


--------------------------------------------------------------------------------
-- xInteger -

-- | uniformly distributed random variable of 'Integer's.
xInteger :: X Integer
xInteger = X $ Action (\(Omega g) -> let (i,g') = R.random g in (i,Omega g'))


-- | uniformly distributed random variable of 'Integer's in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xIntegerB :: Integer -> Integer -> X Integer
xIntegerB l h | h < l = XEmpty
xIntegerB l h = X $ Action (\(Omega g) -> let (i,g') = R.randomR (l,h) g in (i,Omega g'))


--------------------------------------------------------------------------------
-- xChar -

-- | uniformly distributed random variable of 'Char's.
xChar :: X Char
xChar = X $ Action (\(Omega g) -> let (i,g') = R.random g in (i,Omega g'))

-- | uniformly distributed random variable of 'Char's in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xCharB :: Char -> Char -> X Char
xCharB l h | h < l = XEmpty
xCharB l h = X $ Action (\(Omega g) -> let (i,g') = R.randomR (l,h) g in (i,Omega g'))

--------------------------------------------------------------------------------
-- xDouble -

-- | uniformly distributed random variable of 'Double's.
xDouble :: X Double
xDouble = X $ Action (\(Omega g) -> let (i,g') = R.random g in (i,Omega g'))


-- | uniformly distributed random variable of 'Double's in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xDoubleB :: Double -> Double -> X Double
xDoubleB l h | h < l = XEmpty
xDoubleB l h = X $ Action (\(Omega g) -> let (i,g') = R.randomR (l,h) g in (i,Omega g'))

--------------------------------------------------------------------------------
-- xEnum -

-- | uniformly distributed random variable of a 'Bounded' 'Enum' in the range 'minBound'
--   to 'maxBound'.
xEnum :: (Enum a,Bounded a) => X a
xEnum = xEnumB minBound maxBound

-- | uniformly distributed random variable of a 'Enum' in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xEnumB :: Enum a  => a -> a -> X a
xEnumB l h = fmap toEnum (xIntB l' h') where
  l' = fromEnum l
  h' = fromEnum h

--------------------------------------------------------------------------------
-- xBool -

-- | uniformly distributed random variable of 'Bool's.
xBool :: X Bool
xBool = xEnum

--------------------------------------------------------------------------------
-- xZ -

-- | uniformly distributed random variable of 'Z'.
xZ :: X Z
xZ = fmap inj xInteger

--------------------------------------------------------------------------------
-- xZB -

-- | uniformly distributed random variable of 'Z' in the given bounds. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xZB :: Z -> Z -> X Z
xZB l h = fmap inj (xIntegerB (prj l) (prj h))

-------------------------------------------------------------------------------
-- xN -

-- | uniformly distributed random variable in the given range.
xN :: X N
xN = fmap prj xZ -- may be better implementation!

--------------------------------------------------------------------------------
-- xNL -

-- | uniformly distributed random variable bounded by a lower bound.
xNL :: N -> X N
xNL l = fmap (l+) xN

--------------------------------------------------------------------------------
-- xNB -

-- | uniformly distributed random variable in the given range. If the lower
--   bound is greater then the upper bound the result will be 'XEmpty'.
xNB :: N -> N -> X N
xNB l h = fmap prj (xZB (inj l) (inj h)) 

--------------------------------------------------------------------------------
-- xQ -

-- | uniformly distributed random variable of 'Q'.
xQ :: X Q
xQ = fmap (uncurry (%)) (xTupple2 xZ (xNL 1))

--------------------------------------------------------------------------------
-- xOneOf -

toDouble :: Q -> Double
toDouble = fromRational . toRational

-- | @xOneOfW [(w1,x1)..(wn,xn)]@ is the random variable of @x@s in @[x1,x2,..xn]@
-- with a distribution of the @xi@s of @pi = wi/s@, where @0 < n@, @s = w1+w2+..+wn@
-- and @0 <= wi@ for @i = 1..n@. If @n == 0@ then 'XEmpty' will be the result.
xOneOfW :: [(Q,a)] -> X a
xOneOfW = xOneOfW' . fmap (\(w,x) -> (toDouble w,x))
                         
xOneOfW' :: [(Double,a)] -> X a
xOneOfW' []  = XEmpty
xOneOfW' wxs = fmap (to (qxs 0 wxs)) (xDoubleB 0 1)
  where ws  = map fst wxs
        s   = sum ws

        to []          _ = error "OAlg.RandomVariable.xList: empty list!"
        to [(_,x)]     _ = x
        to ((q,x):qxs) p = if p <= q then x else to qxs p

        
        qxs _ []          = []
        qxs sw ((w,x):wxs) = ((sw' / s,x)):qxs sw' wxs
          where sw' = sw + w

-- | @xOneOf xs@ is the random variable of @x@s in @xs@ with a uniformly distribution
--   of the @xi@s, where @0 < length xs@. If @xs == []@ then 'XEmpty' will be the result.
xOneOf :: [a] -> X a
xOneOf [] = XEmpty
xOneOf xs = fmap (axs!) (xIntB 1 n)
  where n = length xs
        axs = array (1,n) (zip [1..] xs)

--------------------------------------------------------------------------------
-- xOneOfXW -

-- | as 'xOneOfW'.
xOneOfXW :: [(Q,X a)] -> X a
xOneOfXW = join . xOneOfW 

--------------------------------------------------------------------------------
-- xOneOfX -

-- | as 'xOneOf'.
xOneOfX :: [X a] -> X a
xOneOfX = join . xOneOf

--------------------------------------------------------------------------------
-- X - MonadPlus -

instance Alternative X where
  empty = XEmpty
  XEmpty <|> xb = xb
  xa <|> XEmpty = xa
  xa <|> xb     = xJoin $ fmap alt xBool where
    alt True  = xa
    alt False = xb

instance MonadPlus X

--------------------------------------------------------------------------------
-- sum' -

-- | a strict and head recursive version of 'sum'.
sum' :: Num x => [x] -> x
sum' xs = sum'' xs 0
  where sum'' []     s = s
        sum'' (x:xs) s = s `seq` sum'' xs (s + x)


--------------------------------------------------------------------------------
-- meanValue - 

-- | the mean value of @n@-samples according the state @s@.
meanValue :: Fractional x => Int -> X x -> Omega -> x
meanValue n xx o = (sum' $ (take n) $ samples xx $ o) / (fromInteger $ toEnum $ n)

--------------------------------------------------------------------------------
-- putDistribution -

-- | puts the distribution according to the given /aspects/ and the given number of samples.
putDistribution' :: (Show x,Ord x) => [x -> String] -> Int -> X x -> Omega -> IO ()
putDistribution' asps n xx = putStatistic asps . take n . samples xx


-- | puts the distribution according of the given number of samples.
putDistribution :: (Show x,Ord x) => Int -> X x -> Omega -> IO ()
putDistribution = putDistribution' []

-- | puts the distribution of according the given number of samples.
putDistributionIO :: (Show x,Ord x) => Int -> X (IO x) -> Omega -> IO ()
putDistributionIO n xx o = (sequence $ take n $ samples xx o) >>= putStatistic []

-- | showing the constructor as an aspect.
aspCnstr :: Show x => x -> String
aspCnstr = takeWhile (/=' ') . show 

--------------------------------------------------------------------------------
-- putDstr -

-- | puts the distribution according of the given number of samples.
putDstr :: (x -> [String]) -> Int -> X x -> IO ()
putDstr asps n xx = getOmega >>= putDistribution n (fmap asps xx)

