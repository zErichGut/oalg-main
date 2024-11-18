
-- |
-- Module      : Main
-- Description : interactive mode for omada.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- the 'main' for the  @omada@-application.
module Main (main) where

import System.Environment
import Control.Exception

import OAlg.Homology.IO.Omada.Definition as Omada

main :: IO ()
main = Omada.repi
