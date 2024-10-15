
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

tween :: a -> [a] -> [a]
tween _ []     = []
tween _ [a]    = [a]
tween d (a:as) = a : d : tween d as

help :: String
help = join $ tween "\n"
  [ "Homology Groups"
  , "---------------"
  , ""
  , "Uage:"
  , ""
  , "  expression = [command | value]"
  , "  command    = \':\' (quit | help) | varbind"
  , "  quit       = \"quit\" | \'q\'"
  , "  help       = \"help\" | \'h\' | \'?\'"
  , "  varbind    = \"let\" var \'=\' value"
  , "  value      = \'H\'| letdecl | zvalue | var"
  , "  letdecl    = \"let\" var \'=\' value \"in\" value"
  , "  zvalue     = z (\'+\' | \'-\'| \'!\') zvalue | \'(\' zvalue \')\' | z"
  , "  z          = [\'-\'] (number | var)"
  , "  var        = char var"
  , "  char       = <any character>"
  , "  number     = digig number"
  , "  digit      = <0..9>"
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
  , "  H 0                homology group for dimension 0"
  ]
