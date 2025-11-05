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
  (
    -- * Lifting
    abhLift, zMatrixLift

    -- * Proposition
  , prpMatrixZJustLiftable
  , prpMatrixZMaybeLiftable
  , prpMatrixZLiftable
  , prpAbhLift

    -- * X
  , xLiftable

  ) where

import Control.Monad

import Data.List (zip,(++))
import Data.Foldable (foldr)

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Number
import OAlg.Structure.Exponential

import OAlg.Entity.Natural hiding ((++))
import OAlg.Entity.Slice.Definition
import OAlg.Entity.Slice.Free
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.PSequence

import OAlg.Adjunction.Definition

import OAlg.AbelianGroup.Free.SmithNormalForm
import OAlg.AbelianGroup.Euclid
import OAlg.AbelianGroup.Definition

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
  | end a /= end y = throw NotLiftable
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
-- abhLift -

-- | liftable abelian homomorphisms with a free end.
--
-- __Property__ Let @a@ and @b@ be in @'Slice' 'To' ('Free' __k__) 'AbHom'@ for some @__k__@, then
-- holds (see diagram below):
--
-- (1) If @'abhLift' (a ':>' b)@ yields @'Just' f@ for some @f@ in @'AbHom', then
-- @'orientation' f '==' a ':>' b@
-- 
-- (2) The following to statements are equivalent:
--
--     (1) There exists an @f@ in @'SliceFactor' 'To' ('Free' __k__) 'AbHom'@ with
--     @'orientation' f '==' a ':>' b@. 
--
--     (2) There exitst an @f@ in 'AbHom' with @'abhLift' (a ':>' b)@ yields @'Just' f@.
--
-- @
--            f
--        * - - - > *
--         \       /
--        a \     / b
--           \   /
--            v v
--             k
-- @
abhLift :: Attestable k
  => Orientation (Slice To (Free k) AbHom) -> Maybe (SliceFactor To (Free k) AbHom)
abhLift (a:>b) = do
  a''  <- zMatrixLift lb a'
  ra'' <- return $ adjr abhFreeAdjunction (start a) a''
  return $ SliceFactor a b $ (i * ra'')
  
  where
    m  = pmap AbHomFree (end a)  -- end a is free!
    a' = adjl abhFreeAdjunction m (slice a)
    lb = amap AbHomFree (slice b)
    i  = abhFreeEmbedding (start b)

--------------------------------------------------------------------------------
-- prpAbhLiftJust -

-- | validity according to 'abhLift'.
prpAbhLift :: N -> Statement
prpAbhLift k = case someNatural k of
  SomeNatural k'
    -> And [ Forall (xoToAbhLiftable k')
               (\otl -> case abhLift otl of
                 Just f  -> And [ valid f
                                , Label "1" :<=>: (orientation f == otl) :?> Params ["a:>b":= show otl
                                                                                    ,"f":= show f
                                                                                    ] 
                                ]
                 Nothing -> Label "2" :<=>: False :?> Params ["a:>b":= show otl]
                            -- otl must be liftable!
               )
           , Forall (xoToAbh k') (valid . abhLift)
           ]

-- | random variable for orientations. They might be not liftable!
xoToAbh :: Any k -> X (Orientation (Slice To (Free k) AbHom))
xoToAbh k = do
  sa <- xStandard
  a  <- xAbHom 1 (sa:>m)
  sb <- xStandard
  b  <- xAbHom 1 (sb:>m)
  return (SliceTo (Free k) a :> SliceTo (Free k) b)
  where m = abg 0 ^ lengthN k
                     
-- | random variable for liftable orientations, i.e. 'abhLift' has to give a solution.
xoToAbhLiftable :: Any k -> X (Orientation (Slice To (Free k) AbHom))
xoToAbhLiftable k = do
  sa <- xStandard
  sb <- xStandard
  b  <- xAbHom 1 (sb :> m)
  f  <- xAbHom 1 (sa :> sb)
  return (SliceTo k' (b*f)  :> SliceTo k' b)
  
  where m  = abg 0 ^ lengthN k
        k' = Free k

-- | validity of 'xoToAbhLiftable'.
vldXoToLiftable :: N -> Statement
vldXoToLiftable k = case someNatural k of SomeNatural k' -> Forall (xoToAbhLiftable k') valid


abhTrv :: AbHom -> String
abhTrv h = if isZero h then "trivial" else "substantial" 

dstXoTo :: Int -> N -> IO ()
dstXoTo n k = case someNatural k of
  SomeNatural k' -> putDstr asp n (amap1 (\ot -> (ot,abhLift ot)) $ xoToAbh k')

  where
    asp :: (Orientation (Slice To (Free k) AbHom), Maybe (SliceFactor To (Free k) AbHom)) -> [String]
    asp (a:>b,mf) = [abhTrv $ slice a, abhTrv $ slice b] ++ case mf of
      Just _  -> ["Just"]
      Nothing -> ["Nothing"]


-- | distribution of /triavial/ or /substantial/ values of 'xoToAbhLiftable'.
dstXoToLiftable :: Int -> N -> IO ()
dstXoToLiftable n k = case someNatural k of
  SomeNatural k' -> putDstr asp n (xoToAbhLiftable k')

  where
    asp :: Orientation (Slice To (Free k) AbHom) -> [String]
    asp (SliceTo _ a :> SliceTo _ b) = [abhTrv a, abhTrv b]

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

-- | validity of 'zMatrixLift'.
prpMatrixZLiftable :: Statement
prpMatrixZLiftable = Prp "MatrixZLiftable" :<=>:
  And [ prpMatrixZJustLiftable xStandardOrtSite
      , prpMatrixZMaybeLiftable (xZB (-1000) 1000)
      ]


