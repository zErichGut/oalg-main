
-- |
-- Module      : Main
-- Description : oalg-exe
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- the 'main' for the  @oalg-exe@.
module Main (main) where

import System.Environment
import Control.Exception

import Lib

import OAlg.Entity.Natural hiding ((++))

--------------------------------------------------------------------------------
-- Flag' -

data Flag' = Flag Flag | Help | Version deriving (Show)

--------------------------------------------------------------------------------
-- version -

version :: String
version = "1.0"

--------------------------------------------------------------------------------
-- someExcp -

-- | catching some exception an returns the given parameter.
someExcp :: x -> SomeException -> IO x
someExcp x _ = return x

--------------------------------------------------------------------------------
-- getFlag -

-- | gets a flag from the list of arguments.
getFlag :: [String] -> IO (Flag',[String])
getFlag (fs@('-':_):ss) = case fs of
  "--help"    -> return (Help,ss)
  "--version" -> return (Version,ss)
  _           -> do
    f <- readFlag fs
    return (Flag f,ss)
    `catch` someExcp (Help,ss)
    
getFlag ss@(_:_) = return (Flag Homlgy,ss)
getFlag ss       = return (Help,ss)

--------------------------------------------------------------------------------
-- putVersion -

putVersion :: IO ()
putVersion = putStrLn ("version: " ++ version)
--------------------------------------------------------------------------------
-- putHelp -

-- | puts the help to 'stdout'.
putHelp :: IO ()
putHelp = do
  putStrLn "oalg - Homology Groups for some Complexes"
  putVersion
  putStrLn ""
  putStrLn "usage: oalg [-h|-c|--help|--version]"
  putStrLn "            (simplex N|sphere N|kleinBottle|torus,moebiusStrip|"
  putStrLn "             projectivePlane)"
  putStrLn ""
  putStrLn "Available options:"
  putStrLn "  -h                     Show the homology groups."
  putStrLn "  -c                     Show the cardinality of the simplex-sets."
  putStrLn "  --help                 Show this help text."
  putStrLn "  --version              Show the version."
  putStrLn ""
  putStrLn "Available complexes:"
  putStrLn "  simplex N              Simplex of dimension N."
  putStrLn "  sphere N               Sphere of dimension N."
  putStrLn "  kleineBottle           Klein Bottle."
  putStrLn "  torus                  Torus of dimension 2."
  putStrLn "  moebiusStrip           Moebius Strip."
  putStrLn ""
  putStrLn "Examples:"
  putStrLn "  oalg-exe kleinBottle   Show the homology groups of the Klein Bottle.."
  putStrLn "  oalg-exe -h torus      Show the homology groups of a 2 dimensional torus."
  putStrLn "  oalg-exe -c sphere 7   Show the cardinality of the simplex-sets of a"
  putStrLn "                         7 dimensional sphere."
  
--------------------------------------------------------------------------------
-- main -

-- | the main function.
main :: IO ()
main = do
  args <- getArgs
  (f',args') <- getFlag args
  case f' of
    Help                  -> putHelp
    Version               -> putVersion
    Flag f                -> case args' of      
      "simplex":sd:_      -> do
        d <- readN sd
        case someNatural d of
          SomeNatural d'  -> putSimplex f d'
      "sphere":sd:_ -> do
        d <- readN sd
        case someNatural d of
          SomeNatural d'  -> putSphere f d'
      "kleinBottle":_     -> putKleinBottle f
      "torus":_           -> putTorus2 f
      "moebiusStrip":_    -> putMoebiusStrip f
      "projectivePlane":_ -> putProjectivePlane f
      _ -> putHelp
   `catch` (\e -> case e of
                    SomeException _ -> putHelp
           )
