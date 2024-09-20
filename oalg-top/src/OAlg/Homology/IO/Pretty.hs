
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
           , DefaultSignatures
#-}


-- |
-- Module      : OAlg.Homology.IO.Interactive
-- Description : pretty printing of values
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- pretty printing of values
module OAlg.Homology.IO.Pretty
  ( Pretty(..)
  ) where

import Data.List ((++))
import Data.Foldable (toList)
import OAlg.Prelude

import OAlg.Data.Either
import OAlg.Data.Symbol

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Ring
-- import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
-- import OAlg.Structure.Vectorial
-- import OAlg.Structure.Exception

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Chain
import OAlg.Homology.Simplex

--------------------------------------------------------------------------------
-- Pretty -

-- | pretty printing of values
class Pretty x where
  pshow :: x -> String
  default pshow :: Show x => x -> String
  pshow = show

--------------------------------------------------------------------------------
-- Basics

instance Pretty N
instance Pretty Z
instance Pretty Symbol
instance Pretty a => Pretty [a] where
  pshow as = case as of
    []   -> "[]"
    a:as -> "[" ++ pshow a ++ ps as ++ "]"
    where
      ps []     = ""
      ps (a:as) = "," ++ pshow a ++ ps as
      
instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pshow (Left a)  = "Left (" ++ pshow a ++ ")"
  pshow (Right b) = "Right (" ++ pshow b ++ ")"

--------------------------------------------------------------------------------
-- Sum

pshowLc :: (Ring r, Pretty r, Pretty a) => String -> LinearCombination r a -> String
pshowLc zero (LinearCombination ras) = ps ras where
  ps []       = zero
  ps (ra:ras) = ps0 ra ++ ps' ras

  ps0 (r,a) | isOne r      = pshow a
            | isMinusOne r = "-" ++ pshow a
            | otherwise    = pshow r ++ "!" ++ pshow a

  ps' []          = ""
  ps' ((r,a):ras) | isOne r      = " + " ++ pshow a ++ ps' ras
                  | isMinusOne r = " - " ++ pshow a ++ ps' ras
                  | otherwise    = " + " ++ pshow r ++ "!" ++ pshow a ++ ps' ras
  

instance (Ring r, Pretty r, Pretty a) => Pretty (Sum r a) where
  pshow s = pshowLc "0" $ smlc s 
                         
instance (Ring r, Pretty r, Pretty a) => Pretty (SumSymbol r a) where
  pshow s = pshowLc "0" $ ssylc s

--------------------------------------------------------------------------------
-- Homology -

instance Pretty x => Pretty (Simplex l x) where
  pshow (Simplex vs) = pshow $ toList vs
  
--------------------------------------------------------------------------------
-- Abelian Group

instance Pretty AbGroup

