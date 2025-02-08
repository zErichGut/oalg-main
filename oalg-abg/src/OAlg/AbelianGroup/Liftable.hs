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
  ( -- * Lifting
    zMatrixLift

    -- * Proposition
  , prpMatrixZJustLiftable
  , prpMatrixZMaybeLiftable
  , prpMatrixZLiftable

    -- * X
  , xLiftable
  ) where

import Control.Monad

import Data.List (zip,(++))
import Data.Foldable (foldr)

import OAlg.Prelude

import OAlg.Data.FinitelyPresentable
import OAlg.Data.Canonical

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Number
import OAlg.Structure.Exponential

import OAlg.Entity.Slice
import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.FinList hiding (zip,(++))
import OAlg.Entity.Diagram
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.PSequence

import OAlg.Limes.Definition
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.Free.SmithNormalForm
import OAlg.AbelianGroup.Euclid

--------------------------------------------------------------------------------
-- abhCokerLft -

-- | the associated liftable, i.e. every cokernel in 'AbHom' has the @'Liftable' 'From'@ property.
--
-- __Property__ Let @coker@ be in @'Cokernel' 'N1' 'AbHom@, than holds:
--
-- (1) @c '==' l@ where @c = 'cokernelFactor' ('universalCone' coker)@ and
-- @'LiftableFrom' c _ = 'abhCokerLft' coker@.
--
-- @
--         c         a
--   * <------- * <------*
--    ^         ^
--     \       /
--   f  \     / f' 
--       \   /
--        \ /
--         *
-- @
--
-- where @c@ is the cokernel of @a@ and @f'@ the lifted @f@. 
abhCokerLft :: Attestable n => Cokernel N1 AbHom -> Liftable From (Free n) AbHom
abhCokerLft coker = LiftableFrom c l where
  c = cokernelFactor $ universalCone coker
  l :: Slice From (Free n) AbHom -> Slice From (Free n) AbHom
  l f | end c /= end (slice f) = throw NotLiftable
      | otherwise              = error "nyi"


{-
--------------------------------------------------------------------------------
-- abhLift -

-- | tries to solve the equation @a '*' x '==' y@, where @'end' y '==' 'end' a@ and @'start' y@ is
-- free of some dimension @__k__@.
--
-- __Property__ Let @a@ be a abelian homomorphisms and @y@ a @'Slice' 'From' ('Free' __k__) 'AbHom'@
-- then holds:
--
-- (1) If @'end' ('slice' y)@ is not equal to @'end' a@ then a 'NotLiftable'-exception will be
-- thrown.
--
-- (2) If @'end' ('slice' y)@ is equal to @'end' a@ and there exists an @x@ in 'AbHom' such that
-- @a '*' 'slice' x '==' 'slice' y@ then the result of @'abhLift' a y@ is @'Just' x@ otherwise it
-- will be 'Nothing'.
abhLift :: AbHom -> Slice From (Free k) AbHom -> Maybe (Slice From (Free k) AbHom)
abhLift = error "nyi"
{-
  this implementation dos not hold the spezification!!!!!!
  try it with the proposition prpAbhLift

abhLift a y@(SliceFrom k _)
  | end a /= end (slice y) = throw NotLiftable "end missmatch"
  | otherwise = case (abgGeneratorTo (start a), abgGeneratorTo (end a)) of
      (   GeneratorTo (DiagramChainTo _ (p:|_)) n _ _ _ _
        , GeneratorTo _ _ _ _ _ lq
        ) -> amap1 ((SliceFrom k) . (p*) . zabh) $ zMatrixLift (abhz a') (abhz y') where

        a' = lq (SliceFrom n (a*p))
        y' = lq y
-}
--------------------------------------------------------------------------------
-- prpAbhLift -

prpAbhLift :: Statement
prpAbhLift = Prp "AbhLift" :<=>:
  Forall ay (\(a,k,y) -> case k of
    SomeNatural k' -> let Just x = abhLift a (SliceFrom (Free k') y) in
      (a * slice x == y) :?> Params ["a":=show a,"y":=show y,"slice x":=show (slice x)]
            )
  where ay = do
          s  <- xStandard
          e  <- xStandard
          a  <- xAbHom 0.8 (s:>e)
          k' <- xNB 0 10
          case finitePresentation abgFinPres s of
            GeneratorTo (DiagramChainTo _ (p:|_)) (Free n) _ _ _ _
              -> let d = dim ()
                     XOrtOrientation _ xMatrixZ = xodZ
                     n' = lengthN n
                  in do
                    x <- xMatrixZ (d^k' :> d^n')
                    let x' = p * zabh x in return (a,someNatural k',a * x')
-}

--------------------------------------------------------------------------------
-- zMatrixLift -

-- | tries to solve the equation @a '*' x '==' y@.
--
-- __Property__ Let @a@ and @y@ be in @'Matrix' 'Z'@, then holds:
--
-- (1) If @'end' y@ is not equal to @'end' a@ then evaluating @'zMatrixLift' a y@ will end up
-- in a 'NotLiftable'-exception.
--
-- (2) If @'end' y@ is equal to @'end' a@ and there exists an @x@ in @'Matrix' 'Z'@ such that
-- @a '*' x '==' y@ then the result of @'zMatrixLift' a y@ is @'Just' x@ otherwise it
-- will be 'Nothing'. If there exists a non trivial solution, then @x@ will also be non trival.
zMatrixLift :: Matrix Z -> Matrix Z -> Maybe (Matrix Z)
zMatrixLift a y
  | end a /= end y = throw NotLiftable "end missmatch"
  | otherwise      = amap1 (r*) $ lft (start a) (ds `zip` [0..]) (s * y) where
  
  DiagonalForm ds (RowTrafo sRT) (ColTrafo rCT) = snfDiagonalForm $ smithNormalForm a
  Inv s _ = amap GLTGL sRT
  Inv r _ = amap GLTGL rCT

  lft :: Dim' Z -> [(Z,N)] -> Matrix Z -> Maybe (Matrix Z)
  lft aCls ds (Matrix _ yCls ys) = do
    y'rc <- lftCols (lengthN aCls) (lengthN yCls) ds (etsrc ys)
    return (Matrix aCls yCls $ rcets y'rc)

  nonTrivialCol :: N -> N -> Closure N -> N -> [(Col N Z,N)]
  nonTrivialCol r aCls yClsReached yCls
    | aCls <= r = [] -- matrix a is injective
    | j' < yCls = [(Col $ PSequence [(1,r)],j')]
    | otherwise = []
    where j' = case yClsReached of
                 NegInf -> 0
                 It j   -> succ j


  lftCols :: N -> N -> [(Z,N)] -> Row N (Col N Z) -> Maybe (Row N (Col N Z))
  lftCols aCls yCls ds rc = do
    (rc',yClsMax) <- foldr (addLftCol ds) (Just ([],NegInf)) $ rowxs rc
    return (Row $ PSequence (rc' ++ nonTrivialCol (lengthN ds) aCls yClsMax yCls))

  addLftCol :: [(Z,N)]
    -> (Col N Z,N) -> Maybe ([(Col N Z,N)],Closure N) -> Maybe ([(Col N Z,N)],Closure N)
  addLftCol ds (yi,j) mCls = do
    (xis,jMax) <- mCls
    xi         <- lftCol ds (colxs yi)
    return ((Col $ PSequence xi,j):xis,It j `max` jMax)

  lftCol :: [(Z,N)] -> [(Z,N)] -> Maybe [(Z,N)]
  lftCol ((d,i):dis) yis@((y,i'):yis') = case i `compare` i' of
    LT -> lftCol dis yis
    EQ -> let (x,r) = divMod y d in case r of
        0 -> lftCol dis yis' >>= return . ((x,i):)
        _ -> Nothing
    -- the case GT should not occure, as the dis are succesive!
  lftCol [] (_:_) = Nothing
  lftCol _ _      = Just []


--------------------------------------------------------------------------------
-- xLiftable -

-- | random variable for liftable samples.
xLiftable :: Multiplicative c => XOrtSite To c -> X (c,c)
xLiftable xTo = amap1 lft $ xMltp2 xTo where lft (Mltp2 a x) = (a,a*x)
  

--------------------------------------------------------------------------------
-- prpMatrixZJustLiftable -

-- | validity of 'zMatrixLift' for liftable samples.
prpMatrixZJustLiftable :: XOrtSite To (Matrix Z) -> Statement
prpMatrixZJustLiftable xTo = Prp "MatrixZJustLiftable" :<=>:
  Forall (xLiftable xTo)
    (\(a,y) -> let mx = zMatrixLift a y in
        case mx of
          Just x -> Label "a * x == y"
                      :<=>: And [ valid x
                                , (a * x == y) :?> Params ["a":=show a,"y":=show y,"x":=show x]
                                ]
          _      -> Label "should be liftable"
                      :<=>: False :?> Params ["a":=show a,"y":=show y]
                     
    )

--------------------------------------------------------------------------------
-- prpMatrixZMaybeLiftable -

-- | validity of 'zMatrixLift' where liftable and unliftable samples are validated.
prpMatrixZMaybeLiftable :: X Z -> Statement
prpMatrixZMaybeLiftable xz = Prp "MatrixZMaybeLiftable" :<=>: Forall ay test where
  ay = do
    a0 <- xz
    a1 <- xz
    y  <- xz
    return (a0,a1,y)

  test (a0,a1,y) = case y `mod` (inj g) of
    0 -> Label "solvable"
           :<=>: case mx of
                   Just x -> And [ valid x
                                 , (a * x == y') :?> Params ["a":=show a,"y":=show y,"x":=show x]
                                 ]
                   _      -> Label "should be solvable"
                               :<=>: False :?> Params ["a":=show a,"y":=show y]
    _ -> Label "unsolvable"
           :<=>: case mx of
                   Nothing -> SValid
                   Just x  -> Label "should be unsolvable"
                     :<=>: False :?> Params ["a":=show a,"y":=show y,"x":=show x]
    where (g,_,_) = euclid a0 a1
          d  = dim () 
          a  = matrix d (d^2) [(a0,0,0),(a1,0,1)]
          y' = matrix d d [(y,0,0)]
          mx = zMatrixLift a y'

--------------------------------------------------------------------------------
-- prpMatrixZLiftable -

-- | validity of 'zLift'.
prpMatrixZLiftable :: Statement
prpMatrixZLiftable = Prp "MatrixZLiftable" :<=>:
  And [ prpMatrixZJustLiftable xStandardOrtSite
      , prpMatrixZMaybeLiftable (xZB (-1000) 1000)
      ]

