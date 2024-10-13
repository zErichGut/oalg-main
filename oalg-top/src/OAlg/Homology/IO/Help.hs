
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
  , "  command    = [\':\' (quit | help) | cvarbind]"
  , "  quit       = \"quit\" | \'q\'"
  , "  help       = \"help\" | \'h\' | \'?\'"
  , "  cvarbind   = \"let\" id \'=\' value"
  , ""
  , "  value      ="
  , ""
  , "Description:"
  , ""
  , "  :quit | :q         exits the program"
  , "  :help | :h | :?    shows this help"
  , "  let x = 0          binds the variable \"x\" to the value 0"
  , ""
  , "Expamples:"
  , ""
  , "  H                  sequence of non-trivial homology groups"
  , "  H 0                homology group of at dimension 0"
  ]
