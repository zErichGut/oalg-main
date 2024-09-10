
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
    (
      readN
    , Flag(..), readFlag

    , putSimplex, putSphere, putKleinBottle, putTorus2, putMoebiusStrip
    , putProjectivePlane

    , iComplex

    ) where

import Control.Monad

import System.IO

import Data.List ((++),reverse,zip)
import Data.Foldable (toList)

import OAlg.Prelude hiding (Result(..))

import OAlg.Data.Canonical
import OAlg.Data.Symbol

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding ((++),zip)
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
  | Interactive Regular -- ^ interactive modus for a given complex 
  deriving (Eq,Show) -- ,Enum,Bounded)

--------------------------------------------------------------------------------
-- readFral -

-- | reads a flag from 'stdin'.
readFlag :: String -> IO Flag
readFlag s = case s of
  "-h"  -> return Homlgy
  "-c"  -> return Card
  "-ir" -> return $ Interactive Regular
  "-it" -> return $ Interactive Truncated
  _     -> error ("unknown flag (-h,-c,-i_):" ++ s)

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
  case ats n of
    Ats -> putHmgGroups (lengthN n) (toList $ hmgGroups $ homology Truncated c)
  where
    n = cpxDim c
    
    putHmgGroups :: N -> [AbGroup] -> IO ()
    putHmgGroups _ []     = hFlush stdout
    putHmgGroups k (g:gs) = do
      putStrLn ("H " ++ show k ++ ": " ++ show g)
      hFlush stdout
      putHmgGroups (pred k) gs
    


--------------------------------------------------------------------------------
-- putCardinality -

-- | puts the cardinality of the simplex-sets of the given complex to 'stdout'.
putCardinality :: Complex n x -> IO ()
putCardinality c = do
  putStrLn "cardinality of simplex-sets:"
  putCard (lengthN $ cpxDim c) c
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
-- Command -

data Command
  = Quit
  | Succ
  | Prev

--------------------------------------------------------------------------------
-- Modus -

data Modus
  = Chains
  | HGroup
  deriving (Show)

--------------------------------------------------------------------------------
-- Result -

data Result
  = Unknown

--------------------------------------------------------------------------------
-- parseCommand -

parseCommand :: String -> IO (Maybe Command)
parseCommand str = case str of
  ":q"    -> return $ Just Quit
  ":succ" -> reutrn $ Just Succ
  ":prev" -> return $ Just Prev
  _       -> return Nothing

--------------------------------------------------------------------------------
-- getCommand -

getCommand :: N -> Modus -> IO (Maybe Command)
getCommand k mds = do
  hPutStr stdout (show mds ++ " " ++ show k ++ "> ")
  hFlush stdout
  hGetLine stdin >>= parseCommand

--------------------------------------------------------------------------------
-- evalCommand -

evalCommand :: Command -> IO (Modus,[(SomeHomology n x,N)],[(SomeHomology n x,N)],Result)
evalCommand = error "nyi"

--------------------------------------------------------------------------------
-- putResult -

putResult :: Result -> IO ()
putResult = error "nyi"

--------------------------------------------------------------------------------
-- iComplex -

-- | intaractive modus for a complex.
iComplex :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> IO ()
iComplex r c = rep HGroup ((reverse $ toList hs) `zip` [0..]) [] where
  ChainHomology hs = homology r c
  -- note: hs is not empty!


  rep :: Modus -> [(SomeHomology n x,N)] -> [(SomeHomology n x,N)] -> IO ()
  rep mds hks@((_,k):_) hks' = do
    mcmd <- getCommand k mds
    case mcmd of
      Just Quit -> return ()
      Just cmd  -> do
        (mds',h'ks,h'ks',res) <- evalCommand cmd
        putResult res
        rep mds' h'ks h'ks'
      Nothing -> do
        hPutStrLn stdout "unknown command!!"
        hFlush stdout
        rep mds hks hks'

      
  rep mds [] (hk:hks) = do
    putStrLn "there is no next homology"
    hFlush stdout
    rep mds [hk] hks

{-    
  rep (hk:hks) [] = do
    putStrLn "there is no previous homology"
    hFlush stdout
    rep 
-}    

--------------------------------------------------------------------------------
-- putSphere -

-- | puts a sphere of the given dimension and according to the given flag to 'stdout'.
putSphere :: Attestable n => Flag -> Any n -> IO ()
putSphere f d = case f of
  Homlgy -> putComplex 7 sphr putHomologyGroups d
  Card   -> putComplex 18 sphr putCardinality d
  Interactive r -> iComplex r (sphr d)
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
  Interactive r -> iComplex r (splx d)
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
    Interactive r -> iComplex r c
  where c = complex kleinBottle

--------------------------------------------------------------------------------
-- putTorus2 -

-- | puts the torus of dimension @2@ and according to the given flag to 'stdout'.
putTorus2 :: Flag -> IO ()
putTorus2 f = do
  case f of
    Homlgy -> putHomologyGroups c
    Card   -> putCardinality c
    Interactive r -> iComplex r c    
  where c = complex $ torus (Set [A,B]) (Set [A,B])

--------------------------------------------------------------------------------
-- putMoebiusStrip -

putMoebiusStrip :: Flag -> IO ()
putMoebiusStrip f = case f of
  Homlgy -> putHomologyGroups c
  Card   -> putCardinality c
  Interactive r -> iComplex r c
  
  where c = complex $ moebiusStrip

--------------------------------------------------------------------------------
-- putProjectivePlane -

putProjectivePlane :: Flag -> IO ()
putProjectivePlane f = case f of
  Homlgy -> putHomologyGroups c
  Card   -> putCardinality c
  Interactive r -> iComplex r c  
  where c = complex $ projectivePlane

