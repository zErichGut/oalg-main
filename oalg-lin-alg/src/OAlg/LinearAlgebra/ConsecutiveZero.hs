
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
  ( -- * Normal Form
    invCnzNormalFormTo
  , ConsZeroNormalForm(..)
  , rowDiagonal

    -- * Proposition
  , prpConsZeroNormalFormTo
  , prpInvCnzNormalFormToQ
  ) where

import Control.Monad

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

import OAlg.Entity.Matrix.Definition
import OAlg.Entity.Matrix.Dim
import OAlg.Entity.Matrix.Entries
import OAlg.Entity.Matrix.Transformation
import OAlg.Entity.Matrix.GeneralLinearGroup

import OAlg.Entity.Natural
import OAlg.Entity.FinList
import OAlg.Entity.Diagram

import OAlg.Limes.Exact.ConsecutiveZero

import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.LinearAlgebra.StepMatrix
import OAlg.LinearAlgebra.KernelsAndCokernels


--------------------------------------------------------------------------------
-- invChainDiagFst -

-- | isomorphism from the given chain diagram to a chain diagram with first matrix a diagonal matrix.
--
-- __Property__ Let @a@ be in @'Diagram' ('Chain' 'To) (__n__ + 1) __n__ ('Matrix' __k__)@ and
-- @i = 'invChainDiagFstTo' d a@ for a @d@ in @'Diagonalizable' __k__@, then holds:
--
-- (1) @a '==' 'start' i@.
--
-- (2) @b0@ is a diagonal matrix, where @b0':|'_ = 'dgArrows' ('end' i)@.
--
-- (3) @f@ is 'one' for all @f@ in @_':|'_':|'fs = 'dgts' ('invFst' i)@.
invChainDiagFstTo :: Distributive k
  => Diagonalizable k -> Diagram (Chain To) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain To) (n+1) n (Matrix k))
invChainDiagFstTo dgz a@(DiagramChainTo _ chs) = case chs of
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
{-
-- | isomorphism from the given chain diagram to a chain diagram with first matrix a diagonal matrix
-- with non zero entries.
invChainDiagFst :: Distributive k
  => Diagonalizable k -> Diagram (Chain t) (n+1) n (Matrix k)
  -> Inv (DiagramTrafo (Chain t) (n+1) n (Matrix k))
invChainDiagFst d a     = case a of
  DiagramChainTo _ _   -> invChainDiagFstTo d a
  DiagramChainFrom _ _ -> error "nyi"
-}

--------------------------------------------------------------------------------
-- invChainDiag -

-- | isomorphism from the given chain-to diagram with consecutive zero matrices to a chain-to diagram
-- with diagonal entries.
invChainDiagTo :: Galoisian k
  => Monic k -> Diagonalizable k
  -> Any n
  -> Diagram (Chain To) (n+1) n (Matrix k) -> Inv (DiagramTrafo (Chain To) (n+1) n (Matrix k))
invChainDiagTo mc@Monic dgz (SW n'@(SW _)) a = let n'Ats = ats n' in case (atsSucc n'Ats,n'Ats) of
  (Ats,Ats) -> γ {- = β * α -} where
--            a0      a1
--     a:   <----- <-----  ...
--     |   |      |      ||
--  α  |   | α0   | α1   || α2 ...
--     |   |      |      ||
--     v   v  b0  v  b1  ||
--     b:   <----- <-----  ...
--     |  ||      |      |
--  β  |  || β0   | β1   | β2 ...
--     |  ||      |      |
--     v  ||  c0  v  c1  v
--     c:   <----- <-----  ...

    -- according to the properties of invChainDiagFstTo and the construction of β it follows that
    -- α2,α3... and β0 are one. As such it is more efficient to compute β * α given by γ.
    γ = Inv γF γS where

      γF = DiagramTrafo a c τs where
        α0:|α1:|_  = dgts $ invFst α
        _ :|β1:|βs = dgts $ invFst β
        
        τs = α0:| β1 * α1:| βs
        
      γS = DiagramTrafo c a τs where
        α0:|α1:|_  = dgts $ invSnd α
        _ :|β1:|βs = dgts $ invSnd β
        
        τs = α0:| α1 * β1:| βs
           
    α = invChainDiagFstTo dgz a
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
    β'@(Inv μ' ν') = invChainDiagTo mc dgz n' b'

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

invChainDiagTo _ dgz _ a = invChainDiagFstTo dgz a

--------------------------------------------------------------------------------
-- rowDiagonal -

-- | predicate for beeing row diagonal.
--
-- __Definition__ A matrix @m@ is __/row diagonal/__ according to @__i0__@, if it has the following
-- form:
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
rowDiagonal :: N -> Matrix x -> Bool
rowDiagonal r m = rd (r,0) (amap1 (\(_,i,j) -> (i,j)) $ etsxs $ mtxxs m) where
  rd ij' (ij:ijs) = (ij' == ij) && rd (succ' ij') ijs
  rd _ _          = True

  succ' (i,j) = (succ i,succ j)

--------------------------------------------------------------------------------
-- ConsZeroNormalForm -

-- | predicate for consecutive zero chain diagrams beeing in normal form.
--
-- __Property__ Let @'ConsZeroNormalForm' c@ be in @t'ConsZeroNormalForm' __t n k__@, then holds:
--
-- (1) @'ConsecutiveZero' c@ is 'valid'.
--
-- (2) If @__t__ ~ 'To'@, then for all @m 0 ':|' m 1 ':|' .. ':|' m l@ in @'dgArrows' c@ holds:
-- @m i@ is @'rowDiagonal' (r i) (m i)@ where @r i@ is defined by: If @1 < i@ then @r i@ is the
-- rank of @m (i - 1)@, otherwise it is @0@.
--
-- (3) If @__t__ ~ 'From'@, then for all @m 0 ':|' m 1 :| ..@ in @'dgArrows' c@ holds:
-- @m i@ is @'colDiagonal' (r i) (m i)@ where @r i@ is defined by: If @i < l@ then @r i@ is the
-- rank of @m (i + 1)@, otherwise it is @0@.
newtype ConsZeroNormalForm t n k = ConsZeroNormalForm (Diagram (Chain t) (n+3) (n+2) (Matrix k))
  deriving (Show,Eq)

--------------------------------------------------------------------------------
-- prpConsZeroNormalFormTo -

-- | validity according to 'ConsZeroNormalForm' for @__t__ ~ 'To'@.
prpConsZeroNormalFormTo :: Distributive k => ConsZeroNormalForm To n k -> Statement
prpConsZeroNormalFormTo (ConsZeroNormalForm c) = Prp "ConsZeroNormalFormTo"
  :<=>: And [ valid (ConsecutiveZero c)
            , vldRwDg 0 0 (dgArrows c)
            ] where

  vldRwDg :: (i ~ N,r ~ N, Distributive k)
    => i -> r -> FinList n (Matrix k) -> Statement
  vldRwDg i r (m:|ms) = And [ rowDiagonal r m :?> Params ["i":=show i, "m":=show m]
                            , vldRwDg (i+1) (rnk m) ms
                            ]
  vldRwDg _ _ _       = SValid
                        
  -- the rank of a diagonal matrix
  rnk :: Matrix x -> N
  rnk (Matrix _ _ xs) = lengthN xs

instance Distributive k => Validable (ConsZeroNormalForm t n k) where
  valid cnf@(ConsZeroNormalForm c) = Label "ConsZeroNormalForm" :<=>: case c of
    DiagramChainTo _ _   -> prpConsZeroNormalFormTo cnf
    DiagramChainFrom _ _ -> prpConsZeroNormalFormTo (ConsZeroNormalForm c') where
      Contravariant2 i   = isoCoMatrixOp
      SDualBi (Left1 c') = amapF i (SDualBi (Right1 c))
    
--------------------------------------------------------------------------------
-- invCnzNormalFormTo -

-- | the normal form of a consecutive zero chain.
--
-- __Property__ Let @c@ be in @'ConsecutiveZero' 'To' __n__ ('Matrix' __k__)@,
-- @iso = 'invCnzNormalFormTo' dgz c@ for @mc@ in @'Monic' __k__@ and
-- @dgz@ in @'Diagonalizable' __k__@, then holds:
--
-- (1) @'start' iso '==' c@.
--
-- (2) Let @d = 'cnzDiagram' ('end' iso)@ and @ds = 'dgArrows' d@, then holds:
-- @'ConsZeroNormalForm' d@ is 'valid'.
invCnzNormalFormTo :: Galoisian k
  => Monic k -> Diagonalizable k
  -> Any n
  -> ConsecutiveZero To n (Matrix k) -> Inv (ConsecutiveZeroHom To n (Matrix k))
invCnzNormalFormTo mc dgz n (ConsecutiveZero a) = toCnzInv $ invChainDiagTo mc dgz (SW (SW n)) a where
  
  toCnzInv :: Inv (DiagramTrafo (Chain To) (n+3) (n+2) (Matrix k))
           -> Inv (ConsecutiveZeroHom To n (Matrix k))
  toCnzInv (Inv t f) = Inv t' f' where
    t' = ConsecutiveZeroHom t
    f' = ConsecutiveZeroHom f

--------------------------------------------------------------------------------
-- prpInvCnzNormalFormToQ -

relInvCnzNormalFormToQ :: (Galoisian k, Attestable n)
  => Monic k -> Diagonalizable k
  -> Any n -> ConsecutiveZero To n (Matrix k) -> Statement
relInvCnzNormalFormToQ mc dgz n c
  = And [ valid iso
        , Label "1" :<=>: (start iso == c) :?> Params ["c":=show c]
        , Label "2" :<=>: valid (ConsZeroNormalForm d)
        ] where

  iso = invCnzNormalFormTo mc dgz n c
  d   = cnzDiagram (end iso)

-- | validity according to 'invCnzNormalFormTo' for matrices over 'Q'.
prpInvCnzNormalFormToQ :: Attestable n => Any n -> Statement
prpInvCnzNormalFormToQ n = Prp "InvCnzNormalFormToQ"
  :<=>: Forall (xCnzToQ n) (relInvCnzNormalFormToQ mncField dgzField n)

--------------------------------------------------------------------------------
-- xCnzToQ -

-- | random variable for 'To'-consecutive zero matrices over 'Q'.
xCnzToQ :: Any n -> X (ConsecutiveZero To n (Matrix Q))
xCnzToQ = xConsZeroTo mtxKernels xStandardOrtOrientation

--------------------------------------------------------------------------------
-- xConsZeroTo -

-- | random variable of 'To'-consecutive zero matrices.
xConsZeroTo :: Distributive x => Kernels N1 (Matrix x) -> XOrtOrientation (Matrix x)
  -> Any n -> X (ConsecutiveZero To n (Matrix x))
xConsZeroTo krs xo n = do
  o  <- xoOrientation xo 
  d0 <- xoArrow xo o
  ds <- xc krs xo (SW n) d0
  return (ConsecutiveZero $ DiagramChainTo (end d0) (d0:|ds))
  
  where
    -- random variable of consecutive zero matrices, where the first matrix is consecutive zero
    -- to the given on.
    xc :: Distributive x
      => Kernels N1 (Matrix x) -> XOrtOrientation (Matrix x)
      -> Any n -> Matrix x -> X (FinList n (Matrix x))
    xc _ _ W0 _        = return Nil
    xc krs xo (SW n) d = do
      s  <- xoPoint xo
      f  <- xoArrow xo (s :> start dk)
      d' <- return (dk * f)
      ds <- xc krs xo n d'
      return (d':|ds)
      where dk = kernelFactor $ universalCone $ limes krs (kernelDiagram d)
 
