
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
  , symbols
  
  ) where

--------------------------------------------------------------------------------
-- keywords of expressions -

alphas
  = [ "let"
    , "H"
    , "span"
    ]

symbols
  = [ "(",")"
    , ":q", ":quit"
    , ":h", ":help", ":?"
    , "+","-"
    , "!"
    , "?"
    , "="
    ]

