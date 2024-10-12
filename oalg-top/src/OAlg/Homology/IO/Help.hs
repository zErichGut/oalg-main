
{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Help
-- Description : help page
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- help page.
module OAlg.Homology.IO.Help
  ( help
  ) where

import Control.Monad

tween :: a -> [[a]] -> [a]
tween d as = tw d as where
  tw :: a -> [[a]] -> [a]
  tw _ []     = []
  tw _ [a]    = a
  tw d (a:as) = a ++ [d] ++ tw d as

help = tween '\n'
  [ "Homology Groups"
  , "---------------"
  , ""
  , "Uage:"
  , ""
  , "  expression = command | value"
  , ""
  , "  command    = \':\' (quit | help) | varbind"
  , "  quit       = \"quit\" | \'q\'"
  , "  help       = \"help\" | \'h\' | \'?\'"
  , ""
  , "  value      ="
  , ""
  , "Description:"
  , ""
  , "  :quit | :q         exits the program"
  , "  :help | :h | :?    shows this help"
  , ""
  , "Expamples:"
  , ""
  , "  H                  evaluates all homology groups"
  , "  H 0                evaluates the homology group of dimension 0"
  ]
