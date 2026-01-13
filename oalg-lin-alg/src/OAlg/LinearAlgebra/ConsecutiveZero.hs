
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.LinearAlgebra.ConsecutiveZero
-- Description : representation for consecutive zeros.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Representation for consecutive zeros.
module OAlg.LinearAlgebra.ConsecutiveZero
  (
  ) where

import Control.Monad (join)
import qualified Data.List as L (zip)
import Data.Foldable

import OAlg.Prelude

import OAlg.Category.SDuality

import OAlg.Data.Singleton
import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring
import OAlg.Structure.Exponential

import OAlg.Entity.Sequence.PSequence

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.LinearAlgebra.StepMatrix

--------------------------------------------------------------------------------

instance XStandardOrtSite To (Matrix Q) where
  xStandardOrtSite = xoTo xStandardOrtOrientation
  

--------------------------------------------------------------------------------
-- Diagonalizable -

-- | predicate for diagonalisable matrices over a @'Distributive' __k__@@.
--
-- __Property__ Let @dg@ be in @'Diagonalizable' __k__@ for a @'Distributive' __k__@, then holds:
--
-- (1) @m '==' 'dgfMatrix' d@ for all @m@ in @'Matrix' __k__@, where @d = 'diagonalForm' dg m@.
newtype Diagonalizable k = Diagonalizable (Matrix k -> DiagonalForm k)

--------------------------------------------------------------------------------
-- prpDiagonalizable -

relDiagonalizable :: Distributive k => Diagonalizable k -> Matrix k -> Statement
relDiagonalizable dg m = valid d && (m == dgfMatrix d) :?> Params ["m":=show m]
  where d = diagonalForm dg m

-- | validity according to t'DiagonalForm'.
prpDiagonalizable :: Distributive k => Diagonalizable k -> X (Matrix k) -> Statement
prpDiagonalizable dg xm = Prp "Diagonalizable" :<=>: Forall xm (relDiagonalizable dg)
  
instance (Distributive k, XStandardOrtOrientation k) => Validable (Diagonalizable k) where
  valid dg = prpDiagonalizable dg (xoOrt xStandardOrtOrientation) 
  
--------------------------------------------------------------------------------
-- diagonalForm -

-- | the associated diagonal form.
diagonalForm :: Diagonalizable k -> Matrix k -> DiagonalForm k
diagonalForm (Diagonalizable d) = d

--------------------------------------------------------------------------------
-- dgzOp -

dgzOp :: Galoisian k => Diagonalizable k -> Diagonalizable (Op k)
dgzOp d = Diagonalizable (dOp toDualOpGal d) where

  -- Matrix (Op k) -> DiagonalForm (Op k)
  dOp :: IsoOpGal k -> Diagonalizable k -> Matrix (Op k) -> DiagonalForm (Op k)
  dOp i d m' = dgfToOp i $ diagonalForm d m where
    m = mtxMapCnt (vInv2 i) m'

  dgfToOp :: IsoOpGal k -> DiagonalForm k -> DiagonalForm (Op k)
  dgfToOp (Contravariant2 i) (DiagonalForm ks rt ct) = DiagonalForm ks' rt' ct' where
    ks' = amap1 (amap i) ks
    rt' = error "nyi"
    ct' = error "nyi"

--------------------------------------------------------------------------------
-- dgzField -

-- | diagonalizables for a @'Field' __k__@.
dgzField :: Field k => Diagonalizable k
dgzField = Diagonalizable mtxDiagonalForm

--------------------------------------------------------------------------------
-- invChainDiagFst -

-- | see 'invChainDiagFst'.
invChainToDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain To) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain To) (n+1) n (Matrix k))
invChainToDiagFst dgz a@(DiagramChainTo _ chs) = case chs of
  Nil     -> one a
  m:|chs' -> Inv t f where
    
    a' = DiagramChainTo (start m) chs'
    b  = DiagramChainTo (end d) (d :| (c' *> chs'))
    os = tail $ amap1 one $ dgPoints a'
    t  = DiagramTrafo a b (r:|c':|os)
    f  = DiagramTrafo b a (r':|c:|os) 

    -- r * m = d * c'
    DiagonalForm ds (RowTrafo rt) (ColTrafo ct) = diagonalForm dgz m  
    Inv r r' = amap GLTGL rt
    Inv c c' = amap GLTGL ct
    d        = diagonal (end m) (start m) ds
    
    -- multiplies the firts entry from the left by the given one.
    (*>) :: Multiplicative x => x -> FinList n x -> FinList n x
    (*>) _ Nil     = Nil
    (*>) l (x:|xs) = (l*x):|xs

-- | isomorphism from the given chain diagram to a chain diagram with first matrix a diagonal matrix
-- with non zero entries.
invChainDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain t) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain t) (n+1) n (Matrix k))
invChainDiagFst d a     = case a of
  DiagramChainTo _ _   -> invChainToDiagFst d a
  DiagramChainFrom _ _ -> error "nyi"

--------------------------------------------------------------------------------
-- Monic -

-- | distributive structures which are monic.
--
-- __Property__ Let @'Monik' __d__@, then holds:
--
-- (1) For all @f@ and @x@ in @__d__@ with @'end' x '==' 'start' f@ and @'not' ('isZero' f)@ holds:
-- If @'isZero' (f '*' x)@ then @'isZero' x@.
class Distributive d => Monic d

--------------------------------------------------------------------------------
-- invChainDiag -

-- | isomorphism from the given chain-to diagram with consecutive zero matrices to a chain-to diagram
-- with diagonal entries.
invChainToDiag :: (Galoisian k, Monic k)
  => Diagonalizable k
  -> Any n
  -> Diagram (Chain To) (n+1) n (Matrix k) -> Inv (DiagramTrafo (Chain To) (n+1) n (Matrix k))
invChainToDiag dgz n@(SW n'@(SW _)) a = let n'Ats = ats n' in case (atsSucc n'Ats,n'Ats) of
  (Ats,Ats) -> β * α where
--            a0      a1
--     a:   <----- <-----  ...
--     |   |      |      |
--  α  |   |      |      | ...
--     v   v  b0  v  b1  v
--     b:   <----- <-----  ...
--     |   |      |      |
--  β  |   |      |      | ...
--     v   v  c0  v  c1  v
--     c:   <----- <-----  ...

    α = invChainToDiagFst dgz a
    β = Inv μ ν

    b          = end α
    b0:|b1:|bs = dgArrows b
    r          = lengthN $ mtxxs b0 -- the rank of b0
    s          = (lengthN $ start b0) >- r 
-- as a is consecutive zero, it follows that:
--   b and c are consecutive zero
--   b0 is diagonal
--   as k is monic it follows that:
--     all rows of b1 with an index i < r are zero

    r' = dim unit ^ r
    s' = dim unit ^ s

    or = one r'
    os = one s'
    p1 = mtxJoin $ matrixBlc [s'] [r',s'] [(os,0,1)]
    i1 = mtxJoin $ matrixBlc [r',s'] [s'] [(os,1,0)]
  
    b'             = DiagramChainTo s' (b'1:|bs) where b'1 = p1 * b1
    β'@(Inv μ' ν') = invChainToDiag dgz n' b'

    c'       = end β'
    c'1:|c's = dgArrows c'
    c        = DiagramChainTo (end b0) (b0:|c1:|c's) where c1 = i1 * c'1
    
    o0 = one (end b0)
    μ  = DiagramTrafo b c μs where
      μs       = o0:| μ''1 :| μ's
      μ'1:|μ's = dgts μ'
      μ''1     = mtxJoin $ matrixBlc [r',s'] [r',s'] [(or,0,0),(μ'1,1,1)] 
    ν  = DiagramTrafo c b νs where
      νs       = o0:| ν''1 :| ν's
      ν'1:|ν's = dgts ν'
      ν''1     = mtxJoin $ matrixBlc [r',s'] [r',s'] [(or,0,0),(ν'1,1,1)] 

invChainToDiag dgz _ a = invChainToDiagFst dgz a

--------------------------------------------------------------------------------
-- ConsZeroNormalForm -

-- | predicate for consecutive zero chain diagrams beeing in normal form.
--
-- __Property__ Let @'ConsZeroNormalForm' c@ be in @t'ConsZeroNormalForm' __t n k__@, then holds:
--
-- (1) @'ConsecutiveZero' c@ is 'valid'.
--
-- (2) If @__t__ ~ 'To'@, then for all @m@ in @'dgArrows' c@ and @s = 'rowHeadIndex' m@ holds:
--
--   (1) For all @(i,j)@ not in @s@ holds: @m i j@ is 'zero'.
--
--   (2) For @(i0,j)':'..@ in @s@ holds: @j '==' 0@. 
--
--   (3) For all @..(i,j)':'(i',j')..@ in @s@ holds: @i' '==' i '+' 1@ and @j' '==' j '+' 1@.
--
-- As such, @m@ has the form:
--
-- @
--           0 1 2 .. r
--      
--          [0 ..             0]
--          ..
--          [0 ..             0]
--  i0      [x0 0 ..          0]
--  i0 + 1  [0 x1 0 ..        0]
--  i0 + 2  [0 0 x2 0 ..      0]
--  ..      ..
--  i0 + r  [0 ..   0 xr 0 .. 0]
--          [0 ..             0]
--          ..  
--          [0 ..             0]
-- @
--
-- (3) If @__t__ ~ 'From'@, then for all @m@ in @'dgArrows' c@ and @s = 'rowHeadIndex' m@ holds:
--
--   (1) For all @(i,j)@ not in @s@ holds: @m i j@ is 'zero'.
--
--   (2) For @(i,j0)':'..@ in @s@ holds: @i '==' 0@. 
--
--   (3) For all @..(i,j)':'(i',j')..@ in @s@ holds: @i' '==' i '+' 1@ and @j' '==' j '+' 1@.
--
newtype ConsZeroNormalForm t n k = ConsZeroNormalForm (Diagram (Chain t) (n+3) (n+2) (Matrix k))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- prpConsZeroNormalFormTo -

-- | validity according to 'ConsZeroNormalForm' for @__t__ ~ 'To'@.
prpConsZeroNormalFormTo :: Distributive k => ConsZeroNormalForm To n k -> Statement
prpConsZeroNormalFormTo (ConsZeroNormalForm c) = Prp "ConsZeroNormalFormTo"
  :<=>: And [ valid (ConsecutiveZero c)
            , foldr (\m v -> vldnf (mtxColRow m) && v) SValid (dgArrows c)
            ] where

  vldnf :: (i ~ N, j ~ N, Show k) => Col i (Row j k) -> Statement
  vldnf (Col (PSequence rws)) = vldRws rws

  vldRws :: (i ~ N, j ~ N, Show k) => [(Row j k,i)] -> Statement
  vldRws []             = SValid
  vldRws rws@((rw,_):_) = And [ Label "2" :<=>: vldRwsHead rw
                              , Label "3" :<=>: vldRwsCons rws
                              ]

  vldRwsHead :: (Show k, j ~ N) => Row j k -> Statement
  vldRwsHead rw@(Row (PSequence xjs)) = case xjs of
    [(_,0)] -> SValid
    _       -> False :?> Params ["rw":=show rw]

  vldRwsCons :: (i ~ N, j ~ N, Show k) => [(Row j k,i)] -> Statement
  vldRwsCons [(Row (PSequence [_]),_)] = SValid
  vldRwsCons ((rw,i):(rw',i'):rws')    = And [ (i' == i + 1) :?> Params ["(i,i')":=show (i,i')]
                                             , vldRwsCon rw rw'
                                             , vldRwsCons ((rw',i'):rws')
                                             ]
  vldRwsCons rws                       = False :?> Params ["rws":=show rws]

  vldRwsCon :: (j ~ N, Show k) => Row j k -> Row j k -> Statement
  vldRwsCon (Row (PSequence [(_,j)])) (Row (PSequence [(_,j')]))
    = (j' == j + 1) :?> Params ["(j,j')":=show (j,j')]
  vldRwsCon rw rw' = False :?> Params ["(rw,rw')":=show (rw,rw')]

instance Distributive k => Validable (ConsZeroNormalForm t n k) where
  valid cnf@(ConsZeroNormalForm c) = Label "ConsZeroNormalForm" :<=>: case c of
    DiagramChainTo _ _   -> prpConsZeroNormalFormTo cnf
    DiagramChainFrom _ _ -> prpConsZeroNormalFormTo (ConsZeroNormalForm c') where
      Contravariant2 i   = isoCoMatrixOp
      SDualBi (Left1 c') = amapF i (SDualBi (Right1 c))
    
--------------------------------------------------------------------------------
-- cnzNormalFormTo -

-- | the normal form of a consecutive zero chain.
--
-- __Property__ Let @c@ be in @'ConsecutiveZero' 'To' __n__ ('Matrix' __k__)@,
-- @dgz@ be a witness of @'Diagonalizable' __k__@ and @iso = 'cnzNormalFormTo' dgz c@ for
-- a @'Monic' __k__@, then holds:
--
-- (1) @'start' iso '==' c@.
--
-- (2) Let @d = 'cnzDiagram' ('end' iso)@ and @ds = 'dgArrows' d@, then holds
--
--     (1) @'ConsZeroNormalForm' d@ is 'valid'.
--
--     (2) @d0@ is a diagonal matrix, where @d0 = 'head' ds@.
--
--     (3) For all @..dk':|'dl..@ in @ds@ holds: @il '==' rk '+' 1@, where
--     @il@ is the first row index of @dl@ with a entry not equal to 'zero' and
--     @rk@ is the last row index of @dk@  with a entry not equal to 'zero' (note: if @dk@ is
--     is 'zero', then @rk@ is defined as @-1@.)
cnzNormalFormTo :: (Galoisian k, Monic k)--, Attestable n)
  => Diagonalizable k
  -> Any n
  -> ConsecutiveZero To n (Matrix k) -> Inv (ConsecutiveZeroHom To n (Matrix k))
cnzNormalFormTo dgz n (ConsecutiveZero a) = toCnzInv $ invChainToDiag dgz (SW (SW n)) a where
  
  toCnzInv :: Inv (DiagramTrafo (Chain To) (n+3) (n+2) (Matrix k))
           -> Inv (ConsecutiveZeroHom To n (Matrix k))
  toCnzInv (Inv t f) = Inv t' f' where
    t' = ConsecutiveZeroHom t
    f' = ConsecutiveZeroHom f


mt :: (Ring r, i ~ N, j ~ N) => N -> N -> [([(r,j)],i)] -> Matrix r
mt r c xijs = matrixTtl r c xijs' where
  xijs' = join $ amap1 (\(xjs,i) -> amap1 (\(x,j) -> (x,i,j)) xjs) xijs

m :: Matrix Q
m = mt 4 6 ([ [2,4,6,0,2  ] `L.zip` [1..]
            , [1,2,3,3,0.5] `L.zip` [1..]
            , [3,6,7,1,2  ] `L.zip` [1..]
            , [1,2,5,3,4/3] `L.zip` [1..]
            ] `L.zip` [0..]
           )

d = DiagramChainTo (end m) (m:|Nil)


xx :: X (Diagram (Chain To) N4 N3 (Matrix Q))
xx = xStandard

pp = Forall xx (valid . invChainDiagFst dgzField)
