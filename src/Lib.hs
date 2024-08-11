
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , RankNTypes
  , DataKinds
#-}

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
import OAlg.Entity.FinList hiding ((++))
import OAlg.Entity.Sequence
import OAlg.Entity.Diagram

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels

import OAlg.Homology.Definition as H
import OAlg.Homology.Simplex
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

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
putHomologyGroups :: (Entity x, Ord x) => Complex n x -> IO ()
putHomologyGroups c = do
  putStrLn "homology groups:"  
  putChnCmplH (cplDim c) c setEmpty (chainComplex c)
  where

    putChnCmplH :: N -> Complex n x -> Set (Simplex (n+1) x) -> ChainComplex From n AbHom -> IO ()
    putChnCmplH d (Vertices s0) s1 h = do
      putH d s1 s0 (ccplHomology abhKernels abhCokernels h)
      return ()      
    putChnCmplH d (Complex s c') s' h = do
      putH d s' s (ccplHomology abhKernels abhCokernels h)
      putChnCmplH (pred d) c' s (ccplPred h)

    putH :: N -> Set (Simplex (n+1) x) -> Set (Simplex n x) -> Homology From n AbHom -> IO ()
    putH d _ _ h = do
      putStrLn ("H " ++ show d ++ ": " ++ (show $ hmlGroup h))
      hFlush stdout

--------------------------------------------------------------------------------
-- putCardinality -

-- | puts the cardinality of the simplex-sets of the given complex to 'stdout'.
putCardinality :: Complex n x -> IO ()
putCardinality c = do
  putStrLn "cardinality of simplex-sets:"
  putCard (cplDim c) c
  where

    putC :: N -> N -> IO ()
    putC d n = putStrLn ("C " ++ show d ++ ": " ++ show n)
  
    putCard :: N -> Complex n x -> IO ()
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
  -> (forall n . Attestable n => Any n -> Complex n x)
  -> (forall n . Complex n x -> IO ())
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
    sphr :: Attestable n => Any n -> Complex n N
    sphr d = complex $ sphere d (0::N)

--------------------------------------------------------------------------------
-- putSimplex -

-- | puts a simplex of the given dimension and according to the given flag to 'stdout'.
putSimplex :: Attestable n => Flag -> Any n -> IO ()
putSimplex f d = case f of
  Homlgy -> putComplex 8 splx putHomologyGroups d
  Card   -> putComplex 19 splx putCardinality d
  where
    splx :: Attestable n => Any n -> Complex n N
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
