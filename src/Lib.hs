
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, RankNTypes #-}

-- |
-- Module      : Lib
-- Description : library for homologies of some complexes.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- library for evaluating the homology groups of some complexes.
module Lib
    ( readN
    , Flag(..), readFlag

    , putSimplex, putSphere, putKleinBottle, putTorus2, putMoebiusStrip
    , putProjectivePlane
    ) where

import Control.Monad

import System.IO

import Data.List ((++))
import Data.Foldable (toList)

import OAlg.Prelude

import OAlg.Data.Canonical
import OAlg.Data.Symbol

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Sequence

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Simplical
import OAlg.Homology.Complex

--------------------------------------------------------------------------------
-- Flag -

-- | flags for evaluation.
data Flag
  = Homlgy -- ^ homology groups.
  | Card -- ^ cardinality of the simplex-sets.
  deriving (Eq,Show,Enum,Bounded)

--------------------------------------------------------------------------------
-- readFral -

-- | reads a flag from 'stdin'.
readFlag :: String -> IO Flag
readFlag s = case s of
  "-h" -> return Homlgy
  "-c" -> return Card
  _    -> error ("unknown flag (-h,-c):" ++ s)

--------------------------------------------------------------------------------
-- readInteger -

-- | reads an integer from 'stdin'.
readInteger :: String -> IO Integer
readInteger = return . read

--------------------------------------------------------------------------------
-- readN -

-- | reads a natural number from 'stdin'.
readN :: String -> IO N
readN s = do
  n <- readInteger s
  return (prj n)
 
--------------------------------------------------------------------------------
-- putHomologyGroups -

-- | puts the homology groups of the given complex to 'stdout'.
putHomologyGroups :: Simplical s x => Complex s n x -> IO ()
putHomologyGroups c = do
  putStrLn "homology groups:"  
  putH (cplDim c) (toList hs)
  where

    Homology hs = homologyGroups c

    putH :: N -> [AbGroup] -> IO ()
    putH _ []     = return ()
    putH d (g:gs) = do
      putStrLn ("H " ++ show d ++ ": " ++ show g)
      hFlush stdout
      putH (pred d) gs

--------------------------------------------------------------------------------
-- putCardinality -

-- | puts the cardinality of the simplex-sets of the given complex to 'stdout'.
putCardinality :: Complex s n x -> IO ()
putCardinality c = do
  putStrLn "cardinality of simplex-sets:"
  putCard (cplDim c) c
  where

    putC :: N -> N -> IO ()
    putC d n = putStrLn ("C " ++ show d ++ ": " ++ show n)
  
    putCard :: N -> Complex s n x -> IO ()
    putCard d (Vertices vs) = putC d (lengthN vs)
    putCard d (Complex ss c) = do
      putC d (lengthN ss)
      hFlush stdout
      putCard (pred d) c

--------------------------------------------------------------------------------
-- putComplex -

-- | puts a complex to 'stdout' according to the given parameters.
putComplex :: Attestable n
  => N
  -> (forall n . Attestable n => Any n -> Complex s n x)
  -> (forall n . Complex s n x -> IO ())
  -> Any n -> IO ()
putComplex n c put d
  | n < lengthN d = do
      putStr ("very time consuming for " ++ show n ++ " < N! proceed? (yes,N): ")
      hFlush stdout
      s <- hGetLine stdin
      case s of
        "yes" -> put (c d)
        sd    -> do
          d <- readN sd
          case someNatural d of
            SomeNatural d' -> putComplex n c put d'
  | otherwise = put (c d)

--------------------------------------------------------------------------------
-- putSphere -

-- | puts a sphere of the given dimension and according to the given flag to 'stdout'.
putSphere :: Attestable n => Flag -> Any n -> IO ()
putSphere f d = case f of
  Homlgy -> putComplex 7 sphr putHomologyGroups d
  Card   -> putComplex 18 sphr putCardinality d
  where
    sphr :: Attestable n => Any n -> Complex Simplex n N
    sphr d = complex $ sphere d (0::N)

--------------------------------------------------------------------------------
-- putSimplex -

-- | puts a simplex of the given dimension and according to the given flag to 'stdout'.
putSimplex :: Attestable n => Flag -> Any n -> IO ()
putSimplex f d = case f of
  Homlgy -> putComplex 8 splx putHomologyGroups d
  Card   -> putComplex 19 splx putCardinality d
  where
    splx :: Attestable n => Any n -> Complex Simplex n N
    splx d = complex $ Set [simplex d (0::N)]
    
--------------------------------------------------------------------------------
-- putKleinBottle -

-- | puts the Klein Bottle according to the given flag to 'stdout'.
putKleinBottle :: Flag -> IO ()
putKleinBottle f = do
  case f of
    Homlgy -> putHomologyGroups c
    Card   -> putCardinality c
  where c = complex kleinBottle

--------------------------------------------------------------------------------
-- putTorus2 -

-- | puts the torus of dimension @2@ and according to the given flag to 'stdout'.
putTorus2 :: Flag -> IO ()
putTorus2 f = do
  case f of
    Homlgy -> putHomologyGroups c
    Card   -> putCardinality c
  where c = complex $ torus (Set [A,B]) (Set [A,B])

--------------------------------------------------------------------------------
-- putMoebiusStrip -

putMoebiusStrip :: Flag -> IO ()
putMoebiusStrip f = case f of
  Homlgy -> putHomologyGroups c
  Card   -> putCardinality c
  where c = complex $ moebiusStrip

--------------------------------------------------------------------------------
-- putProjectivePlane -

putProjectivePlane :: Flag -> IO ()
putProjectivePlane f = case f of
  Homlgy -> putHomologyGroups c
  Card   -> putCardinality c
  where c = complex $ projectivePlane
