
{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : OAlg.Data.Statistics
-- Description : a tool kit for making statistics
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- a tool kit for making statistics.
module OAlg.Data.Statistics
  ( -- * Statistic
    mkStatisticW, mkStatistic, putStatisticW, putStatistic
  )
  where

import Prelude hiding (lookup)

import Data.List (sort, sortBy, groupBy)

import OAlg.Control.Verbose

import OAlg.Data.Equal

----------------------------------------
-- mkStatisticW -

-- | makes the statistics of the given list of wight, value pairs.
mkStatisticW :: Ord x => [x -> String] -> [(Int,x)] -> (Int,[(Double,[String],x)])
mkStatisticW asp xs = ( n'
                      , sort
                      $ map aggr  
                      $ groupBy (eql cmpsnd)
                      $ sortBy cmpsnd
                      $ map nrml                    -- [(n,([String],x))]
                      $ zip (map (apply asp) xs) xs -- [([String],(n,x))]
                      )
  where n' = sum $ map fst xs
        n  = toEnum n'
        
        apply []     _ = []
        apply (a:as) x = (a $ snd x) : apply as x

        nrml (asp',(n'',x)) = (n'',(asp',x))

        cmpsnd a b = compare (snd a) (snd b)

        aggr axs@((_,(a,x)):_) = (w,a,x)
          where w = (toEnum $ sum $ map fst axs) / n

----------------------------------------
-- mkStatistic -

-- | makes the statistics of the given list of values.
mkStatistic :: Ord x => [x -> String] -> [x] -> (Int,[(Double,[String],x)])
mkStatistic asp xs = mkStatisticW asp (map (\x -> (1,x)) xs)

----------------------------------------
-- putStatistic -

-- | puts the statistics of the given list of wight, values pairs.
putStatisticW :: (Show x, Ord x) => [x -> String] -> [(Int,x)] -> IO ()
putStatisticW asps xs = do
  putStrLn ("statistic of " ++ show n ++ " elements")
  sequence_ $ map putLnElm $ sts
  where (n,sts) = mkStatisticW asps xs
        putLnElm (w,as,x) = do
          putStr (vshow Middle (Percent w))
          putStr " "
          putStr (if as == [] then "" else (show as ++ " "))
          putStr "-> "
          putStr (show x)
          putStr "\n"

----------------------------------------
-- putStatistic -

-- | puts the statistics of the given list of values.
putStatistic :: (Show x, Ord x) => [x -> String] -> [x] -> IO ()
putStatistic asp xs = putStatisticW asp (map (\x -> (1,x)) xs)


