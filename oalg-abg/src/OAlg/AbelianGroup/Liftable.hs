{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds, RankNTypes #-}

-- |
-- Module      : OAlg.AbelianGroup.Definition
-- Description : lifting of abelian homomorphisms.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- lifting of abelian homomorphisms.
module OAlg.AbelianGroup.Liftable
  () where

import Control.Monad

import Data.List (zip)

import OAlg.Prelude

import OAlg.Data.Generator

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number

import OAlg.Entity.Slice
import OAlg.Entity.FinList hiding (zip)
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.PSequence

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.Free.SmithNormalForm

--------------------------------------------------------------------------------
-- abhLift -

-- | trying to solve the equation @a '*' x '==' y@, where @'end' y '==' 'end' a@ and @'start' y@ is
-- free of some dimension @__k__@.
--
-- __Property__ Let @a@ be a abelian homomorphisms and @y@ a @'Slice' 'From' ('Free' __k__) 'AbHom'@
-- then holds:
--
-- (1) If @'end' ('slice' y)@ is not equal to @'end' a@ then a 'NotLiftable'-exception will be
-- thrown.
--
-- (2) If @'end' ('slice' y)@ is equal to @'end' a@ and there exists an @x@ in 'AbHom' such that
-- @a '*' x '==' 'slice' y@ then the result of @'abhLift' a y@ is @'Just' x@ otherwise it will be
-- 'Nothing'.
abhLift :: AbHom -> Slice From (Free k) AbHom -> Maybe (Slice From (Free k) AbHom)
abhLift a y@(SliceFrom k _)
  | end a /= end (slice y) = throw NotLiftable "end missmatch"
  | otherwise = case (abgGeneratorTo (start a), abgGeneratorTo (end a)) of
      (   GeneratorTo (DiagramChainTo _ (p:|_)) n _ _ _ _
        , GeneratorTo (DiagramChainTo _ (q:|_)) _ _ _ _ lq
        ) -> amap1 ((SliceFrom k) . (p*) . zabh) $ zLift (abhz a') (abhz y') where

        a' = lq (SliceFrom n (a*q))
        y' = lq y

--------------------------------------------------------------------------------
-- zLift -

zLift :: Matrix Z -> Matrix Z -> Maybe (Matrix Z)
zLift a y
  | end a /= end y = throw NotLiftable "end missmatch"
  | otherwise = amap1 (rInv *) $ lft (start a) (ds `zip` [0..]) (sInv * y) where
  
  DiagonalForm ds (RowTrafo sRT) (ColTrafo rCT) = snfDiagonalForm $ smithNormalForm a
  Inv _ sInv = amap GLTGL sRT
  Inv _ rInv = amap GLTGL rCT

  lft :: Dim' Z -> [(Z,N)] -> Matrix Z -> Maybe (Matrix Z)
  lft n ds (Matrix _ yCls ys) = do
    y'rc <- lftCols ds (etsrc ys)
    return (Matrix n yCls $ rcets y'rc)

  lftCols :: [(Z,N)] -> Row N (Col N Z) -> Maybe (Row N (Col N Z))
  lftCols ds rc = do
    rc' <- lftCols' ds $ rowxs rc
    return (Row $ PSequence rc')

  lftCols' :: [(Z,N)] -> [(Col N Z,N)] -> Maybe [(Col N Z,N)]
  lftCols' _ []           = Just []
  lftCols' ds ((y,j):yjs) = do
    y'js <- lftCols' ds yjs
    y'   <- lftCol ds (colxs y)
    return ((Col (PSequence y'),j):y'js)
    

  lftCol :: [(Z,N)] -> [(Z,N)] -> Maybe [(Z,N)]
  lftCol ((d,i):dis) yis@((y,i'):yis')
    | i < i'   = lftCol dis yis
    | otherwise = let (x,r) = divMod y d in case r of
        0 -> lftCol dis yis' >>= return . ((x,i):)
        _ -> Nothing
  lftCol [] (_:_) = Nothing
  lftCol _ _      = Just []
        

