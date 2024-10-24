
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
  ( alphas
  , symbols
  , comment
  ) where

--------------------------------------------------------------------------------
-- keywords of expressions -

-- | the key-words.
alphas :: [String]
alphas
  = [ "let", "in", "ext"
    , "A", "B", "C", "H", "K"
    , "h", "d", "d'"
    ]

-- | the symbols.
symbols :: [String]
symbols
  = [ "(",")"
    , ":quit", ":q" 
    , ":help", ":h", ":?"
    , ":load", ":l"
    , "+","-", "!"
    , "=", "#"
    ]

-- | the comment-symbol string. Everything after this symbol will be ignored by the lexer until
--   the end of line.
comment :: String
comment = "//"
