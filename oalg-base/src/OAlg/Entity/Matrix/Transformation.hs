
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}

-- |
-- Module      : OAlg.Entity.Matrix.Transformation
-- Description : elementary matrix transformations
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- elementary matrix transformations, i.e. operations of 'GLT' on 'Matrix'.
module OAlg.Entity.Matrix.Transformation
  ( -- * Row Trafo
    RowTrafo(..), crTrafoRows

    -- * Col Trafo
  , ColTrafo(..), crTrafoCols

    -- * Diagonal Form
  , DiagonalForm(..), dgfMatrix
  , DiagonalFormStrictPositive(..)
  )

  where

import Control.Monad

import Data.List (length,map)

import OAlg.Prelude

import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Number
import OAlg.Structure.Ring
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Product

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.GeneralLinearGroup

--------------------------------------------------------------------------------
-- crShearRows -

-- | shears tow rows of a /matrix/.
--
--   __Pre__ @k '<' l@.
crShearRows :: (Distributive x, Ord i, Ord j)
  => i -> i -> GL2 x
  -> Col i (Row j x) -> Col i (Row j x)
crShearRows k l (GL2 s t u v) = colShear (*>) (<+>) k l s t u v where

  _ *> Nothing   = Nothing
  a *> (Just rw) = just (not.rowIsEmpty) (a `rowMltl` rw)

  a <+> Nothing     = a
  Nothing <+> b     = b
  Just a <+> Just b = just (not.rowIsEmpty) (a `rowAdd` b)

--------------------------------------------------------------------------------
-- crShearCols -

-- | shears the tow columns of a /matrix/.
--
--   __Pre__ @k '<' l@.
crShearCols :: (Distributive x, Ord j)
  => j -> j -> GL2 x
  -> Col i (Row j x) -> Col i (Row j x)
crShearCols k l (GL2 s t u v) rws
  = colFilter (not.rowIsEmpty) $ fmap (rowShear (<*$) (<+>) k l s t u v) rws where
  
  Nothing <*$ _  = Nothing
  (Just x) <*$ r = just (not.isZero) (x*r) 

  a <+> Nothing     = a
  Nothing <+> b     = b
  Just a <+> Just b = just (not.isZero) (a+b) 

--------------------------------------------------------------------------------
-- crScaleRow -

crScaleRow :: (Distributive x, Ord i)
  => i -> Inv x -> Col i (Row j x) -> Col i (Row j x)
crScaleRow i a cl = colScale (*>) i (inj a) cl where
  a *> rw = just (not.rowIsEmpty) (a `rowMltl` rw)

--------------------------------------------------------------------------------
-- crScaleCol -

crScaleCol :: (Distributive x, Ord j)
  => j -> Inv x -> Col i (Row j x) -> Col i (Row j x)
crScaleCol j a rws
  = colFilter (not.rowIsEmpty) $ fmap (rowScale (<*$) j (inj a)) rws where
  x <*$ s = just (not.isZero) (x*s)

--------------------------------------------------------------------------------
-- rcScaleCol -

rcScaleCol :: (Distributive x, Ord j)
  => j -> Inv x -> Row j (Col i x) -> Row j (Col i x)
rcScaleCol j a cls = rowScale (<*$) j (inj a) cls where
  cl <*$ a = just (not.colIsEmpty) (cl `colMltr` a)

--------------------------------------------------------------------------------
-- rcShearCols -

rcShearCols :: (Distributive x, Ord i, Ord j)
  => j -> j -> GL2 x
  -> Row j (Col i x) -> Row j (Col i x)
rcShearCols k l (GL2 s t u v) = rowShear (<*$) (<+>) k l s t u v where
  Nothing <*$ _   = Nothing
  (Just cl) <*$ a = just (not.colIsEmpty) (cl `colMltr` a)
  
  a <+> Nothing     = a
  Nothing <+> b     = b
  Just a <+> Just b = just (not.colIsEmpty) (a `colAdd` b)

--------------------------------------------------------------------------------
-- crTrafoRows -

-- | applying a transformation as a row transformation on a column of rows.
crTrafoRows :: Transformation x -> Col N (Row N x) -> Col N (Row N x)
crTrafoRows (Permute _ _ p) rws = rws <* p
crTrafoRows (Scale _ k s) rws   = crScaleRow k s rws
crTrafoRows (Shear _ k l g) rws = crShearRows k l g rws

--------------------------------------------------------------------------------
-- crTrafoCols -

-- | applying a transformation as a column transformation on a column of rows.
crTrafoCols :: Col N (Row N x) -> Transformation x -> Col N (Row N x)
crTrafoCols rws (Permute _ _ p) = amap1 (<*p') rws where p' = invert p
crTrafoCols rws (Scale _ k s)   = crScaleCol k s rws
crTrafoCols rws (Shear _ k l g) = crShearCols k l g rws

--------------------------------------------------------------------------------
-- rcTrafoCols -

-- | applying a transformation as a column transformation on a row of columns.
rcTrafoCols :: Row N (Col N x) -> Transformation x -> Row N (Col N x)
rcTrafoCols cls (Permute _ _ p) = cls <* p' where p' = invert p
rcTrafoCols cls (Scale _ k s)   = rcScaleCol k s cls
rcTrafoCols cls (Shear _ k l g) = rcShearCols k l g cls

--------------------------------------------------------------------------------
-- ColTrafo -

-- | 'GLT' as a column transformation.
newtype ColTrafo x = ColTrafo (GLT x)  
  deriving ( Eq,Show,Validable,Entity
           , Multiplicative, Invertible, Cayleyan
           )

instance Oriented x => Oriented (ColTrafo x) where
  type Point (ColTrafo x) = Dim x (Point x)
  orientation (ColTrafo t) = orientation t

instance Oriented x => Exponential (ColTrafo x) where
  type Exponent (ColTrafo x) = Z
  ColTrafo t ^ z = ColTrafo (t^z)

--------------------------------------------------------------------------------
-- ColTrafo - OrientedOpr -

instance Oriented x => Opr (ColTrafo x) (Matrix x) where
  Matrix r c xs <* (ColTrafo t)
    | d == c    = Matrix r (start t) (rcets (etsrc xs <| inj t))
                  -- for a justification for the expression inj t see rdcGLTForm
                  -- respectively the properties of GLT 
    | otherwise = throw NotApplicable
    where d    = end t 
          (<|) = prfopr' n rcTrafoCols
          n    = 10 `max` (lengthN d `div` 2)

instance Distributive x => OrientedOpr (ColTrafo x) (Matrix x)

--------------------------------------------------------------------------------
-- RowTrafo -

-- | 'GLT' as row transformations.
newtype RowTrafo a = RowTrafo (GLT a)
  deriving ( Eq,Show,Validable,Entity
           , Multiplicative, Invertible, Cayleyan
           )

instance Oriented a => Oriented (RowTrafo a) where
  type Point (RowTrafo a) = Dim a (Point a)
  orientation (RowTrafo t) = orientation t

instance Oriented a => Exponential (RowTrafo a) where
  type Exponent (RowTrafo a) = Z
  RowTrafo t ^ z = RowTrafo (t^z)

--------------------------------------------------------------------------------
-- RowTrafo - OrientedOpl -

instance Oriented x => Opl (RowTrafo x) (Matrix x) where
  RowTrafo t *> Matrix r c xs
    | d == r    = Matrix (end t) c $ crets (inj t |> etscr xs)
                  -- for a justification for the expression inj t see rdcGLTForm
                  -- respectively the properties of GLT 
    | otherwise = throw NotApplicable
    where d = start t
          (|>) = prfopl' n crTrafoRows
          n    = 10 `max` (lengthN d `div` 2)

instance Distributive x => OrientedOpl (RowTrafo x) (Matrix x)

--------------------------------------------------------------------------------
-- DiagonalForm -

-- | the result of transforming a matrix into a diagonal form.
--
-- __Property__ Let @'DiagonalForm' ds rt ct@ be in @'DiagonalForm' __k__@, then holds:
--
-- (1) @n '<=' 'lengthN' ('start' rt)@ and @n '<=' 'lengthN' ('end' ct)@ where
-- @n = 'lengthN' ds@.
--
-- (2) For all @d@ in @ds@ holds: @'not' ('isZero' d)@.
data DiagonalForm k = DiagonalForm [k] (RowTrafo k) (ColTrafo k) deriving (Eq,Show)

--------------------------------------------------------------------------------
-- DiagonalForm - Entity -

instance Distributive k => Validable (DiagonalForm k) where
  valid (DiagonalForm ds rt ct) = Label "DiagonalForm" :<=>:
    And [ valid (ds,rt,ct)
        , Label "1" :<=>:
            (lengthN ds <= min (lengthN (start rt)) (lengthN (end ct)))
              :?>Params[ "lengthN ds":=show (length ds)
                       , "lengthN (start rt)":= show (lengthN (start rt))
                       , "lengthN (end ct)":=show (lengthN (end ct))
                       ]
        , Label "2"
            :<=>: (and $ map (not.isZero) ds) :?>Params ["ds":=show ds]
        ]

instance Distributive k => Entity (DiagonalForm k)

--------------------------------------------------------------------------------
-- dgfMatrix -

-- | the resulting matrix by applying on the diagonal matrix the inverse of the
-- given transformations.
dgfMatrix :: Distributive k => DiagonalForm k -> Matrix k
dgfMatrix (DiagonalForm ds rt ct) = (rt'*>dm)<*ct' where
  rt' = invert rt
  ct' = invert ct
  dm = diagonal (start rt') (end ct') ds


--------------------------------------------------------------------------------
-- DiagonalFormStrictPositive -

-- | predicate for diagonal forms with strict positive entries.
--
-- __Property__ Let @'DiagonalFormStrictPositive' ('DiagonalForm' ds _ _)@ be in
-- @'DiagonalForm' __k__@, then holds: @0 '<' d@ for all @d@ in @ds@. 
newtype DiagonalFormStrictPositive k
  = DiagonalFormStrictPositive (DiagonalForm k)
 deriving (Show,Eq)

instance Number k => Validable (DiagonalFormStrictPositive k) where
  valid (DiagonalFormStrictPositive f@(DiagonalForm ds _ _))
    = Label "DiagonalFormStrictPositive" :<=>:
      And [ valid f
          , vld (0::N) ds
          ] where
    vld _ []     = SValid
    vld i (d:ds) = And [ (rZero < d):?> Params ["(d,i)":=show (d,i)]
                       , vld (succ i) ds
                       ]
                   
instance Number k => Entity (DiagonalFormStrictPositive k)

