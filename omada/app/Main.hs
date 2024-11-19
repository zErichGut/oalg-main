module Main (main) where

import Control.Monad

import Omada.Definition
import Omada.Util

logo :: String
logo = join $ tween "\n" 
  [ "------------------------------------------"
  , ""
  , "                               o"
  , "   o   o    o  o    oo o    ooo    oo o"
  , "  o  o  o   o  o   o  o    o  o   o  o"
  , "   oo oo    o o     oo o    oo     oo o"
  , "           o"
  , ""
  , "------------------------------------------"
  ]

version :: String
version = "1.0"

intro :: String
intro = join $ tween "\n"
  [ ""
  , logo
  , ""
  , "Version: " ++ version
  , ""
  , "Exploring the homology groups of the chain complex derived from an `abstract` simplical complex."
  , ""
  , "For a short introduction just enter ':tutorial'and to quit the application ':quit'. For further"
  , "help enter ':help'."
  , ""
  ]


main :: IO ()
main = do
  putStrLn intro
  repli
