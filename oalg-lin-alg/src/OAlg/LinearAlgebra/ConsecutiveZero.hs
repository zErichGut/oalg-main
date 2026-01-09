
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

import OAlg.Data.Either
import OAlg.Data.Variant

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Ring

import OAlg.Entity.Sequence.PSequence

import OAlg.Entity.Matrix.Definition
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
-- isoChainDiagFst -

-- | isomorphism from the given chain diagram to a chain diagram with first matrix a diagonal matrix
-- with non zero entries.
isoChainToDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain To) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain To) (n+1) n (Matrix k))
isoChainToDiagFst dgz a@(DiagramChainTo _ chs) = case chs of
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

isoChainDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain t) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain t) (n+1) n (Matrix k))
isoChainDiagFst d a     = case a of
  DiagramChainTo _ _   -> isoChainToDiagFst d a
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
-- ConsZeroNormalForm -

-- | predicate for consecutive zero chain diagrams beeing in normal form.
--
-- __Property__ Let @'ConsZeroNormalForm c@ be in @t'ConsZeroNormalForm' __t n k__@, then for all
--  holds:
--
-- (1) @'ConsecutiveZero' c@ is 'valid'.
--
-- (2) If @__t__ ~ 'To'@, then for all @m@ in @'dgArrows' c@ and @s = 'rowHeadIndex' m@ holds:
--
--   (1) For all @(i,j)@ not in @s@ holds: @m i j@ is 'zero'.
--
--   (2) For @(_,j)':'..@ in @s@ holds: @j '==' 0@. 
--
--   (3) For all @..(i,j)':'(i',j')..@ in @s@ holds: @i' '==' i '+' 1@ and @j' '==' j '+' 1@.
--
-- As such, @m@ has the form:
--
-- @
--    [0 ..           0]
--    ..
--    [0 ..           0]
--    [x0 0 ..        0]
--    [0 x1 0 ..      0]
--    [0 0 x2 0 ..    0]
--    ..
--    [0 .. 0 xr 0 .. 0]
--    [0 ..           0]
--    ..
--    [0 ..           0]
-- @
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
-- @d@ be a witness of @'Diagonalizable' __k__@ and @i = 'cnzNormalFormTo' d c@ for @'Monic' __k__@,
-- then holds:
--
-- (1) @'start' i '==' c@.
--
-- (2) @'ConsZeroNormalForm' ('end' i)@ is 'valid'.
cnzNormalFormTo :: Monic k
  => Diagonalizable k
  -> ConsecutiveZero To n (Matrix k) -> Inv (ConsecutiveZeroHom To n (Matrix k))
cnzNormalFormTo = error "nyi"


{-
    chs'' = case chs' of
      Nil   -> Nil
      _:|cs -> c':|cs 
-}

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

pp = Forall xx (valid . isoChainDiagFst dgzField)
