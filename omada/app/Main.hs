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
  , "Exploring the homology groups of the chain complex, given by an `abstract` simplical complex."
  , ""
  , "For further help enter ':help' and to quit the application ':quit'."
  , ""
  , "*** have fun ***"
  , ""
  ]


main :: IO ()
main = do
  putStrLn intro
  repli
