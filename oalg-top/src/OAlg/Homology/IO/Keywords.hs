
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
-- Module      : OAlg.Homology.IO.Keywords
-- Description : keywors
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- keywords
module OAlg.Homology.IO.Keywords
  ( -- * Alphas
    alphas
    
   -- * Symbols
  , sympols
  
  ) where

--------------------------------------------------------------------------------
-- keywords of commands -

kwQuit = "quit"
kwHelp = "help"

--------------------------------------------------------------------------------
-- keywords of expressions -
kwHomologyGroups = "H"
kwSpan           = "span"

alphas
  = [ -- commands
      kwQuit
    , kwHelp
    
      -- expressions
    , kwHomologyGroups
    , kwSpan
    ]

sympols
  = [ "(",")"
    , ":"
    , "+","-"
    , "!"
    ]

