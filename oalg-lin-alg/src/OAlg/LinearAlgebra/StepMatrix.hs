
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}

-- |
-- Module      : OAlg.LinearAlgebra.StepMatrix
-- Description : reducing to step matrices.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Reducing matrices over fields to step matrices.
module OAlg.LinearAlgebra.StepMatrix
  (
    -- * Step Matrix
    stepMatrix, stepMatrixPre, StepMatrix(..)
  , stepGraph, StepGraph(..), stgxs
  , crHeadIndex

    -- * Diagonal Form
  , mtxDiagonalForm

    -- * Proposition
  , prpStepMatrixQ, prpStepMatrix
  , prpMtxDiagonalFormQ, prpMtxDiagonalForm
  ) where


import Control.Monad (join)
import Data.List as L (head,tail,zip,foldl,foldr,span)

import OAlg.Prelude

import OAlg.Data.Constructable
import OAlg.Data.Canonical
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Ring
import OAlg.Structure.PartiallyOrdered
import OAlg.Structure.Exponential
import OAlg.Structure.Operational

import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sequence.Graph
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.Permutation
import OAlg.Entity.Product

import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup

--------------------------------------------------------------------------------
-- rowHeadIndex -

-- | graph of the head indices, i.e. assignment of each row index @i@ the corresponding
-- head index @j@.
--
-- Let @'Col' rws@ be in @'Col' __i__ ('Row' __j x__)@
--
-- pre: for each row @rw@ in @rws@ holds: @rw@ is not empty.
crHeadIndex :: Col i (Row j x) -> Graph i j
crHeadIndex (Col (PSequence xi)) = Graph $ amap1 hij xi where
  hij :: (Row j x,i) -> (i,j)
  hij (Row (PSequence xij),i) = (i,snd $ head xij)

-- | graph of the head indices, i.e. assignment of each row index @i@ the corresponding
-- head index @j@.
--
-- __Note__ If the given matrix is zero, then the resulting graph is empty.
rowHeadIndex :: (i ~ N, j ~ N) => Matrix x -> Graph i j
rowHeadIndex (Matrix _ _ xij) = crHeadIndex $ etscr xij

--------------------------------------------------------------------------------
-- StepGraph -

-- | predicate for a 'Graph' beeing a /step function/.
--
-- __Property__ Let @'StapGraph' s@ be in @'StepGraph' 'N' 'N'@ and let
-- @s = '['(i0,_)..(i,j),(i',j')..']'@ then holds:
--
-- (1) The sequence of the domain indices starts at @0@ and is successive, i.e.
--  @i0 '==' 0@ and @i' '==' i '+' 1@,
--
-- (2) Teh sequence of the range indices are strict increasing, i.e. @j '<' j'@.
newtype StepGraph i j = StepGraph (Graph i j) deriving (Show,Eq,LengthN)

instance Validable (StepGraph N N) where
  valid (StepGraph (Graph ijs)) = Label "StepGraph" :<=>: vldSGraph 0 ijs where
    vldSGraph _ []          = SValid
    vldSGraph n ((i,j):ijs) = And [ Label "1" :<=>: (n == i) :?> Params ["n":=show n, "i":=show i]
                                  , case ijs of
                                      []       -> SValid
                                      (_,j'):_ -> And [ Label "2" :<=>: (j < j')
                                                           :?> Params [ "i" :=show i
                                                                      , "j" :=show j
                                                                      , "j'":=show j'
                                                                      ]
                                                      , vldSGraph (succ n) ijs
                                                      ]
                                  ]
--------------------------------------------------------------------------------
-- stgxs -

-- | the underlying associations.
stgxs :: StepGraph i j -> [(i,j)]
stgxs (StepGraph (Graph ijs)) = ijs

--------------------------------------------------------------------------------
-- StepMatrix -

-- | predicate for a 'Matrix' beeing in /step form/.
--
-- __Properties__ Let @m@ be in @'StepMatrix' __k__@ for a @'Ring' __k__@, then holds:
--
-- (1) the associated 'stepGraph' is 'valid@.
--
-- (2) For all @i@ in the domain of @s = 'stepGraph' m@ holds:
--
--    (1) @m i (s i) '==' 'rOne'@
--
--    (2) @m i' (s i) '==' 'rZero@ for all @i' '/=' i@,
newtype StepMatrix k = StepMatrix (Matrix k) deriving (Show,Eq)

instance Semiring k => Validable (StepMatrix k) where
  valid m@(StepMatrix m') = Label "StepMatrix" :<=>:
    And [ valid m'
        , Label "1" :<=>: valid $ stepGraph m
        , vldStpRws s' (etscr rws)
        ] where

    StepGraph (Graph s') = stepGraph m
    Matrix _ _ rws = m'

    vldStpRws [] _ = SValid -- as such, rws is empty, i.e all entries are zero
    vldStpRws ((i,j):ijs) (Col (PSequence rws))
      = And [ Label "2.1" :<=>: (xij == rOne) :?> Params ["(i,j)":=show (i,j),"xij":=show xij]
            , Label "2.2" :<=>: ((j's && js) == empty)
                :?> Params ["(i,j)":=show (i,j),"j's":= show (j's && js)]
                    
            , vldStpRws ijs (Col $ PSequence $ rws')
            ] where
        -- tail and head bellow are well defined, becaus (i,j):jis is not empty and
        -- are given by rowHeadIndex
        Row (PSequence rwi) = fst $ head rws
        xij                 = fst $ head rwi
        rws'                = tail rws
        j's                 = Set $ amap1 snd rwi
        js                  = Set $ amap1 snd ijs                 
        
--------------------------------------------------------------------------------
-- stepGraph -

-- | the associated step graph
stepGraph :: StepMatrix x -> StepGraph N N
stepGraph (StepMatrix m) = StepGraph $ rowHeadIndex m

sf = StepMatrix (matrix (dim () ^ 7) (dim () ^ 5) [(1,0,1),(1,1,3),(2,1,4),(3,0,2)]) :: StepMatrix N

--------------------------------------------------------------------------------
-- stepMatrix -

-- | transforming a matrix by row transformations to step form.
--
-- __Property__ Let @m@ be in @'Matrix' __k__@ for a @'Field' __k__@ and let
-- @('StepMatrix' m',t) = 'stepMatrix' m@, then holds:
--
-- (1) @t '*>' m' '==' m@.
stepMatrix :: Field k => Matrix k -> (StepMatrix k, RowTrafo k)
stepMatrix m@(Matrix dr dc _) = (StepMatrix $ Matrix dr dc xij',t) where
  (cls,tfs) = stepMatrixPre m
  xij'      = rcets cls
  t         = RowTrafo $ amap FTGLT $ make tfs
  
type TF k     = ProductForm Z (Transformation k)

-- | transforming a matrix by row transformations to a row of columns in step form. This is the
-- pre evaluation for 'stepMatrix'.
stepMatrixPre :: (Field k, i ~ N, j ~ N) => Matrix k -> (Row j (Col i k),TF k)
stepMatrixPre (Matrix dr _ xij) = crStepMtx dr 0 (etscr xij)


crStepMtx :: (i ~ N, j ~ N, Field k) => Dim' k -> i -> Col i (Row j k) -> (Row j (Col i k),TF k)
crStepMtx dr i rws = crStepMtx' dr i (crHeadIndex rws) rws

-- let crStepMtx' dr i ijs (rws,tfs)
--
-- pre: - ijs = crHeadIndex rws
crStepMtx' :: (i ~ N, j ~ N, Field k)
  => Dim' k -> i -> Graph i j -> Col i (Row j k) -> (Row j (Col i k),TF k)
crStepMtx' dr _ (Graph []) _    = (rowEmpty,One dr)  -- ijs is empty implies that rws is empty!
crStepMtx' dr i (Graph ijs) rws = (j,cl',tfs') >:* crStepMtx' dr i' (crHeadIndex rws') rws' where
  j  = foldl min (snd $ head ijs) (amap1 snd ijs)
  cl = crHeadColAt j rws

  (i',cl',tfs') = clNormalForm dr i cl
  rws'          = tfs' *> crTailRowsAt j rws

  (>:*) :: (j,Col i k,GLT k) -> (Row j (Col i k),TF k) -> (Row j (Col i k),TF k)
  (j,cl,tf) >:* (cls,tfs) = ((cl,j)>:cls,tfs :* toTF tf) where
    toTF :: GLT k -> TF k
    toTF = (inj :: ProductForm N a -> ProductForm Z a) . inj

  (>:) :: (Col i k,j) -> Row j (Col i k) -> Row j (Col i k)
  clj >: Row (PSequence cls) = Row (PSequence (clj:cls))

  -- applying the row transformations 
  (*>) :: (i ~ N, j ~ N) => GLT k -> Col i (Row j k) -> Col i (Row j k)
  t *> rws = prfopl crTrafoRows (inj t) rws where

  -- reduces the column to its normal form.
  clNormalForm :: (i ~ N, Field k) => Dim' k -> i -> Col i k -> (i,Col i k,GLT k)
  clNormalForm dr i cl@(Col (PSequence xi)) = let (xil,xih) = L.span ((<i) . snd) xi in case xih of
    []           -> (i,cl,one dr)
    (x,i'):xih'  -> (succ i,Col (PSequence [(rOne,i)]),tfs) where
      tfs = amap FTGLT $ make (  tElims tElimh dr i xih'
                              :* tElims tEliml dr i xil
                              :* tScale dr i x'
                              :* tSwap dr i i'
                              )
      x'  = Inv (invert x) x  -- x is not zero!

      tSwap :: (i ~ N, Ring k) => Dim' k -> i -> i -> TF k
      tSwap d i i' = P $ Permute d d (swap i i')
    
      tScale :: (i ~ N, Ring k) => Dim' k -> i -> Inv k -> TF k
      tScale d i x = P $ Scale d i x
    
      tElims :: (Dim' k -> i -> (k,i) -> TF k) -> Dim' k -> i -> [(k,i)] -> TF k
      tElims shr d i = foldr (:*) (One d) . amap1 (shr d i)

      -- let t = tElim d i (x,i')
      -- pre : i' < i
      tEliml :: (i ~ N, Field k) => Dim' k -> i -> (k,i) -> TF k
      tEliml d i (x,i') = P $ Shear d i' i (GL2 rOne (negate x) rZero rOne) 

      -- let t = tElim d i (x,i')
      -- pre : i < i'
      tElimh :: (i ~ N, Field k) => Dim' k -> i -> (k,i) -> TF k
      tElimh d i (x,i') = P $ Shear d i i' (GL2 rOne rZero (negate x) rOne)

-- m = matrix (dim () ^ 7) (dim () ^ 5) [(2,1,0),(4,3,0),(7,1,1)] :: Matrix Q

mt :: (Ring r, i ~ N, j ~ N) => N -> N -> [([(r,j)],i)] -> Matrix r
mt r c xijs = matrixTtl r c xijs' where
  xijs' = join $ amap1 (\(xjs,i) -> amap1 (\(x,j) -> (x,i,j)) xjs) xijs

m :: Matrix Q
m = mt 4 6 ([ [2,4,6,0,2  ] `zip` [1..]
            , [1,2,3,3,0.5] `zip` [1..]
            , [3,6,7,1,2  ] `zip` [1..]
            , [1,2,5,3,4/3] `zip` [1..]
            ] `zip` [0..]
           )

--------------------------------------------------------------------------------
-- prpStepMatrix -

-- | validity according to 'stepMatrix'.
prpStepMatrix :: Field k => Matrix k -> Statement
prpStepMatrix m = Prp "StepMatrix" :<=>:
  And [ valid s
      , valid t
      , Label "1" :<=>: (t *> m == m') :?> Params ["m'":=show m',"t":=show t] 
      ] where
  (s@(StepMatrix m'),t) = stepMatrix m

-- | validity of transforming matrices over 'Q' with the given maximal dimension to 'stepMatrix'.
prpStepMatrixQ :: Statement
prpStepMatrixQ = Prp "StepMatrixQ" :<=>: Forall xQ prpStepMatrix where
  xQ :: X (Matrix Q)
  xQ = xOneOfXW [ (2/5,xoOrt $ xMatrixTtl 5 1 xStandard)
                , (2/5,xoOrt $ xMatrixTtl 16 0.8 xStandard)
                , (1/5,xoOrt $ xMatrixTtl 100 0.01 $ xOneOf [-1,1])
                ]

--------------------------------------------------------------------------------
-- mtxDiagonalForm -

-- | transforming a matrix to its diagonal form.
--
-- __Property__ Let @m@ be a matrix over a @'Field' __k__@ and @d = 'mtxDiagonal' m@, then holds:
--
-- (1) @'dgfMatrix' d '==' m@.
mtxDiagonalForm :: Field k => Matrix k -> DiagonalForm k
mtxDiagonalForm (Matrix rs cs xijs) = DiagonalForm dg rt ct where
  toOp = toDualOpGal -- the duality operator on the type k.

  dg = amap1 fst $ rcDiags dis
  rt = RowTrafo $ amap FTGLT $ make rtfs
  ct = ColTrafo $ amap FTGLT $ make $ tfsFromOp toOp ctfs'

  (xijs',ctfs') = crStepMtx (dimToOp toOp cs) 0 (etsToOp toOp xijs)
  (dis,rtfs)    = crStepMtx rs 0 (rcFromOp toOp xijs')

  dimToOp :: Ring k => IsoOpGal k -> Dim' k -> Dim' (Op k)
  dimToOp (Contravariant2 t) = dimMap (pmap t)

  -- the transposed entries as a column of rows
  etsToOp :: (Ord j, Ord i) => IsoOpGal k -> Entries i j k -> Col j (Row i (Op k))
  etsToOp t = etscr . etsMapCnt t

  -- the transposed row of columns as a column of rows.
  rcFromOp :: i ~ j => IsoOpGal k -> Row j (Col i (Op k)) -> Col i (Row j k)
  rcFromOp = rcTranspose . vInv2

  -- the transposed transformations.
  tfsFromOp :: IsoOpGal k -> TF (Op k) -> TF k
  tfsFromOp = pdfTrMapCnt . vInv2

--------------------------------------------------------------------------------
-- prpMtxDiagonalForm -

-- | validity according to 'mtxDiagomlForm'.
prpMtxDiagonalForm :: Field k => Matrix k -> Statement
prpMtxDiagonalForm m = Prp "MtxDiagonalForm"
  :<=>: (dgfMatrix d == m) :?> Params ["m":=show m,"d":=show d]
  where d = mtxDiagonalForm m

--------------------------------------------------------------------------------
-- prpMtxDiagonalForm -

-- | validity according to 'mtxDiagomlForm' for some matrices over 'Q',
prpMtxDiagonalFormQ :: Statement
prpMtxDiagonalFormQ = Prp "MtxDiagonalFromQ"
  :<=>: Forall xQ prpMtxDiagonalForm where
  xQ :: X (Matrix Q)
  xQ = xoOrt $ xMatrixTtl 16 0.8 xStandard

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

