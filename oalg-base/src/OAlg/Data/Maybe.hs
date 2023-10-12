
-- |
-- Module      : OAlg.Data.Maybe
-- Description : maybe predicate
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Maybe.
module OAlg.Data.Maybe
  ( module M
  , just
  , exstJust
  )
  where

import Data.Maybe as M

--------------------------------------------------------------------------------
-- exstJust -

-- | gets all the 'Just's - if there are any.
exstJust :: [Maybe v] -> Maybe [v]
exstJust mvs = case catMaybes mvs of
  [] -> Nothing
  vs -> Just vs

--------------------------------------------------------------------------------
-- jsut -

-- | @just p a '==' 'Just' a@ if and only if @p a@.
just :: (a -> Bool) -> a -> Maybe a
just p a = if p a then Just a else Nothing

