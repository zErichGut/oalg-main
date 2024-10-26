
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
  , "  command    = quit | help | load | varbind"
  , "  quit       = ':quit' | ':q'"
  , "  help       = ':help' | ':h' | ':?'"
  , "  load       = (':load' | ':l') cpxId"
  , "  cpxId      = 'empty' | 'kleineBottle' | 'sphere' num"
  , "  varbind    = 'let' var '=' value"
  , "  value      = [sigs] term [('+' | '-'| '!') value]"
  , "  sigs       = ('+' | '-') sigs"
  , "  term       = letdecl | atom [term]"
  , "  letdecl    = 'let' var '=' value 'in' value"
  , "  atom       = 'A' | 'B'| 'C'| 'H'| 'K'"
  , "             | '#' | 'd' | 'd'' | 'h'"
  , "             | num | var | '(' value ')"
  , "  var        = char var"
  , "  char       = <any character>"
  , "  num        = dig num"
  , "  dig        = <0..9>"
  , ""
  , "Description:"
  , ""
  , "  :quit | :q         exits the program"
  , "  :help | :h | :?    shows this help"
  , "  let x = 0          binds the variable 'x' to the value 0"
  , ""
  , "Expamples:"
  , ""
  , "  H                  sequence of non-trivial homology groups"
  , "  H 0                homology group for dimension 0"
  , "  C                  sequence of chain generators"
  , "  C 0                seqence of chain generators for dimension 0"
  , "  C 1 3              the 3rd chain generator for dimension 1"
  , "  D                  sequence of cycle generators"
  , "  L                  sequence of homology group generators as chains"
  , "  E                  sequence of homology group generators as homoloy class"
  ]
