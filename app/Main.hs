
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

import OAlg.Entity.Natural

--------------------------------------------------------------------------------
-- someExcp -

-- | catching some exception an returns the given parameter.
someExcp :: x -> SomeException -> IO x
someExcp x _ = return x

--------------------------------------------------------------------------------
-- getFlag -

-- | gets a flag from the list of arguments.
getFlag :: [String] -> IO (Maybe Flag,[String])
getFlag (fs@('-':_):ss) = case fs of
  "--help" -> return (Nothing,ss)
  _        -> do
    f <- readFlag fs
    return (Just f,ss)
    `catch` someExcp (Nothing,ss)
    
getFlag ss = return (Nothing,ss)

--------------------------------------------------------------------------------
-- putHelp -

-- | puts the help to 'stdout'.
putHelp :: IO ()
putHelp = do
  putStrLn "oalg - Some Homology Groups"
  putStrLn ""
  putStrLn "usage: oalg [-h|-c|--help]"
  putStrLn "            (simplex N|sphere N|kleinBottle|torus)"

  
--------------------------------------------------------------------------------
-- main -

-- | the main function.
main :: IO ()
main = do
  args <- getArgs
  (mf,args') <- getFlag args
  case mf of
    Nothing -> putHelp
    Just f  -> case args' of      
      "simplex":sd:_ -> do
        d <- readN sd
        case someNatural d of
          SomeNatural d' -> putSimplex f d'
      "sphere":sd:_ -> do
        d <- readN sd
        case someNatural d of
          SomeNatural d' -> putSphere f d'
      "kleinBottle":_ -> do
        putKleinBottle f
      "torus":_ -> do
        putTorus2 f
      _ -> putHelp
   `catch` (\e -> case e of
                    SomeException _ -> putHelp
           )
