
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
-- Module      : Omada.Help
-- Description : help page
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- help page.
module Omada.Help
  ( help
  ) where

import Control.Monad

import Omada.Util

help :: String
help = join $ tween "\n"
  [ "Usage:"
  , ""
  , "  instruction = [command | expression]"
  , ""
  , "  command     = quit | help | setcpx | load | varbind"
  , "  quit        = ':quit' | ':q'"
  , "  help        = ':help' | ':h' | ':?'"
  , "  setcpx      = (':complex' | ':c') cpxid"
  , "  cpxid       = 'empty' | 'kleineBottle' | 'moebiusStrip'"
  , "              | 'torus' num | 'projectiveSpace' num | 'simplex' num"
  , "              | 'sphere' num | 'plane' num num"
  , "  load        = (':load' | ':l' ) filepth"
  , "  varbind     = 'let' var '=' expression"
  , ""
  , "  expression  = [sigs] term [('+' | '-'| '!') expression]"
  , "  sigs        = ('+' | '-') sigs"
  , "  term        = letdecl | atom [term]"
  , "  letdecl     = 'let' var '=' expression 'in' expression"
  , "  atom        = 'D' | 'C' | 'H'| 'K' | 'L'| '#' | 'b' | 'd' | 'h'"
  , "              | num | var | '(' expression ')"
  , ""
  , "  filepth     = '\"' [chrs] '\"'"
  , "  var         = chrs"
  , "  chrs        = chr [chrs]"
  , "  chr         = <any character>"
  , "  num         = dig [num]"
  , "  dig         = <0..9>"
  , ""
  , "Description:"
  , ""
  , "  :complex cpx       sets the 'cpx' as the actual simplical complex."
  , "  :quit | :q         exits the program."
  , "  :help | :h | :?    shows this help."
  , "  :load \"foo\"        loads the instructions containing in the file 'foo'."
  , "  let x = 0          binds the variable 'x' to the expression zero."
  , ""
  , "  H                  sequence of homology groups of the chain complex, given by the actual"
  , "                     simplical complex. Its n-th component 'H n' denotes the n-th homology group."
  , "                     Note: Entering just 'H' will display only the non-trivial groups."
  , "  C                  matrix of chains, where 'C n' denotes the sequence of n-simplices of the"
  , "                     actual complex and 'C n i' the i-th simplex (starting from 0) of 'C n'."
  , "                     'C' together with the boundary operator 'd' (see below) form the"
  , "                     chain complex of the actual simplical complex."
  , "  D                  matrix of chains, where 'D n' denotes a sequence of generators for the"
  , "                     abelian group of n-cycles and 'D n i' the i-th cycle of 'D n'."
  , "  L                  matrix of chains, where 'L n' denotes a sequence of n-cycles, such that"
  , "                     there homology classes - i.e. 'h (L n)' - is a generator for the"
  , "                     n-th homology group."
  , "  K                  matrix of homology classes, where 'K n' is a generator for the"
  , "                     n-th homology group. Note: 'K' is equivalent to 'h D'."  
  , ""
  , "  d                  the boundary operator, which assigns to each chain its boundary"
  , "  b                  the ´inverse´ boundary operator, which tries to find a (n+1)-chain 'x' for"
  , "                     a given n-cycle 'y'. such that 'd x' is equal to 'y'."
  , "  h                  the homology class operator, which assigns to each cycle its"
  , "                     homology class."
  , "  #                  the span operator, which assigns to each sequence the lowest and the"
  , "                     highest index of the non-trivial components."
  , ""
  , "Examples:"
  , ""
  , "  H 0                the simplical homology group at dimension zero for the actual simplical"
  , "                     complex."
  , "  # H                the span of 'H'."
  , ""
  , "  C 0                the vertices of the actual simplical complex."
  , "  C 0 2              the third vertex of the actual simplical complex (counting starts at 0)."
  , "  D 1 0 - D 1 1      the subtraction of the first minus the second 1-cycle of the actual"
  , "                     simplical complex."
  , "  2!D 2 0            the scalar multiplication of the first 2-cycle with 2."
  , ""
  , "  d (C 2 0)          the boundary of 'C 2 0'."
  , "  d (C 1)            the sequence of boundaries of 'C 1'"
  , "  d (d C)            the sequence of boundaries of the boundaries of 'C', which is zero."
  , "  h (D 1 4)          the homology class of the 1-cycle 'D 1 4'."
  , "  b (D 2 1 - D 2 0)  if the homology class of 'D 2 1 - D 2 0' is zero, then"
  , "                     'b (D 2 1 - D 2 0)' is a 3-chain 'x', such that 'd x' is equal to"
  , "                     'D 2 1 - D 2 0', otherwise the result will be a failure."  
  , ""
  , "Note:"
  , " - As the computational complexity can grow very fast and if one is interested only in some"
  , "   special homology groups, it is recommended to evaluate this groups directly by entering"
  , "   'H n' insted of 'H'."
  , " - Many grammatically valid expressions will end up in a failure, because they do not evaluate to"
  , "   a meaningful value. For example:"
  , "     - 'C 1 0 + C 2 0' will end up in a failure, because 1-chains and 2-chains are not addable!"
  , "     - 'C 1 0 0' will end up in a failure, because the matrix 'C' is applied to to many"
  , "       parameters!"
  , "     - 'D d' will end up in a failure, because applying the matrix 'D' to the boundary operator"
  , "       makes no sens!"
  ]

