
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE
    TypeFamilies
  , TypeOperators
  , MultiParamTypeClasses
  , FlexibleInstances
  , FlexibleContexts
  , GADTs
  , StandaloneDeriving
  , GeneralizedNewtypeDeriving
  , DataKinds
  , RankNTypes
#-}

-- |
-- Module      : OAlg.Homology.ChainComplex
-- Description : the variance of a complex.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- the variance of a chain complex, i.e. the measure of beeing exact.
module OAlg.Homology.Variance
  (
    -- * Variance
    Variance(..)
  , ccxZFromVariance, ccxZToVariance
  
  , Variance'(..)
  , ccxVariance'

  
  , vrcHomologyClass, vrcBoundary, vrcBoundary'
  , R, S, S', S'', T, T'
  , vrcC, vrcT', vrcT'', vrck

    -- * Generators
  , vrcCyclesGen, vrcHomologyGroupGen

  ) where

import Control.Monad

import Data.Foldable (toList)
import Data.List (filter)

import OAlg.Prelude hiding (T)

import OAlg.Data.Either
import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Oriented
import OAlg.Structure.Multiplicative
import OAlg.Structure.Additive
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Natural as N
import OAlg.Entity.FinList as F 
import OAlg.Entity.Diagram as D
import OAlg.Entity.Matrix hiding (Transformation(..))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Slice

import OAlg.Limes.Cone
import OAlg.Limes.Definition
import OAlg.Limes.Limits
import OAlg.Limes.KernelsAndCokernels

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Liftable

import OAlg.Homology.ChainComplex


import OAlg.Homology.Complex
import OAlg.Homology.Simplical
import OAlg.Category.Map
import OAlg.Structure.Ring
import OAlg.Structure.Multiplicative
--------------------------------------------------------------------------------
-- Variance -

type R   = Slice From 
type S   = Slice From
type S'  = Slice From
type S'' = Slice From
type T   = Slice From
type T'  = Slice From


-- | measures the variance of the top chain complex of being exact. The function
-- 'boundary' evaluates according to a given 'Variance' a possible /boundary/ for a given /cycle/.
--
-- @
--
--
--                         b            c
-- top       p  :    r ---------> s -------------> t
--           ^       ^            ^                ^
--           |       |            |                |
--           | u     | one        | k = ker c      | 0
--           |       |            ^                |
-- center    p' :    r -------->  s' ----------->> t'
--           ^       ^     b'     ^  c' = coker b' ^
--           |       |            |                |
--           | u'    | one        | k' = ker c'    | 0
--           |       |            ^                ^
-- bottom    p'':    r --------> s'' ------------> t''
--                        b''       c'' = coker b''
-- @
--
-- __Note__ In the case that @__d__@ represents finaly generated abelian groups it follows that
-- @s''@ represents the image of @b@ and hence @b''@ is surjective. Further more if @s@ is free
-- it follows that @s''@ is also free and hence one can use 'zMatrixLift' for free @r@ and @s@.
data Variance i d where
  Variance
    :: Diagram (Chain To) N3 N2 (Transformation (Chain From) N3 N2 d)

       -- | the universal property of the kernel of @c@. Let @s@ be in @'Slice' 'From' __i__ __c__@
       -- with @'end' s '==' 'start' c@ then holds:
       -- If @c '*>' s@ is not zero then the result is @'Left' (c'*>'s)@
       -- otherwise the universal factor of the kernel of @c@. __Note__ If the premise
       -- @'end' s '==' 'start' c@ dose not hold, then the evaluation will end up in a
       -- algebraic exception.
    -> (S (i N1) d -> Either (T (i N1) d) (S' (i N1) d))

       -- | the universal property of the kernel of @c'@. Let @s'@ be in @Slice From i c@ with
       -- @end s' == start c'@ then holds: If @c' *> s'@ is not zero then the result is @Left (c'*>s')@
       -- otherwise the universal factor of the kernel of @c'@.
    -> (S' (i N1) d -> Either (T' (i N1) d) (S'' (i N1) d))

       -- | the liftable property of @b''@. Let @s@ be in @Slice From (i N1) c@ with @end s == end b''@
       -- then the result is the lifted @s@.
    -> (S'' (i N1) d -> R (i N1) d)

      -- | the liftable property of @c'@.
    -> (forall k . Sliced (i k) d => Any k -> T' (i k) d -> Either () (S' (i k) d))
    -> Variance i d


instance Distributive d => Validable (Variance i d) where
  valid (Variance d3x3 _ _ _ _) = Label "Variance" :<=>:
    And [ valid d3x3
        , valid $ amap1 ChainComplex $ dgPoints $ d3x3
        ]

--------------------------------------------------------------------------------
-- vrcC -

-- | the arrow @c@ in the diagram of 'Variance'.
vrcC :: Distributive d => Variance i d -> d
vrcC  (Variance (DiagramChainTo _ (u:|_)) _ _ _ _) = case end u of
    DiagramChainFrom _ (_:|c:|_) -> c
    
--------------------------------------------------------------------------------
-- vrcT' -

-- | the point @t'@ in the diagram of 'Variance'.
vrcT' :: Distributive d => Variance i d -> Point d
vrcT' (Variance (DiagramChainTo _ (u:|_)) _ _ _ _) = case start u of
    DiagramChainFrom _ (_:|c':|_) -> end c'

--------------------------------------------------------------------------------
-- vrcT'' -

-- | the point @t''@ in the diagram of 'Variance'.
vrcT'' :: Distributive d => Variance i d -> Point d
vrcT'' (Variance (DiagramChainTo _ (_:|u':|_)) _ _ _ _) = case start u' of
    DiagramChainFrom _ (_:|c'':|_) -> end c''

--------------------------------------------------------------------------------
-- vrck -

-- | the kernel factor @k@ in the diagram of 'Variance'.
vrck :: Variance i d -> d
vrck (Variance (DiagramChainTo _ (u:|_)) _ _ _ _) = case trfs u of
  _:|k:|_ -> k

--------------------------------------------------------------------------------
-- (<>) -

(<>) :: (Distributive d, Sliced (i N1) d)
  => (Slice From (i k) d -> FinList k (Slice From (i N1) d))
     -> Slice From (i k) d -> [Slice From (i N1) d]
(<>) splt = filter (not . isZero) . toList . splt


--------------------------------------------------------------------------------
-- vrcCyclesGen -

-- | a set of gererators of the kernel of @c@.
vrcCyclesGen :: (Distributive d, Ord d, Sliced (i N1) d, i ~ Free)
  => Variance i d
  -> FinitelyPresentable To i d
  -> Splitable From i d
  -> Set (S (i N1) d)
vrcCyclesGen v@(Variance _ _ _ _ _) gen sp = case kGen of
    SomeSliceN g -> set (split sp <> (k *> g))
  where
    k    = vrck v
    kGen = generator $ finitePresentation gen $ start k

--------------------------------------------------------------------------------
-- vrcHomologyClass -

-- | tries to evaluate the homology class of a given chain.
--
--  __Property__ Let @v@ be in @'Variance' __i__ __c__@ and @s@ in @'S' __i__ __c__@ with
--  @'end' s == start c@ (see diagram in 'Variance'), then holds:
--
--  (1) If @t = c *> s@ is not zero, then the result is @('Left' t)@, otherwise
--
--  (2) The result is @c' '*>' s'@, where @s'@ is the induce factor given by @s@.
vrcHomologyClass :: Distributive d
  => Variance i d -> S (i N1) d -> Either (T (i N1) d) (T' (i N1) d)
vrcHomologyClass (Variance d3x3 cKerUnv _ _ _) s = do
  s' <- cKerUnv s
  return (c' *> s')
  where
    _:|c':|_ = dgArrows $ start $ head $ dgArrows $ d3x3

--------------------------------------------------------------------------------
-- vrcHomologyGroupGen -

-- | a set of cycles, generating the homology group.
vrcHomologyGroupGen :: (Distributive d, Ord d, Sliced (i N1) d, i ~ Free)
  => Variance i d
  -> FinitelyPresentable To i d
  -> Splitable From i d
  -> Set (S (i N1) d)
vrcHomologyGroupGen v@(Variance _ _ _ _ c'Lft) gen sp = case t'Gen of
    SomeSliceN t'Gen -> case c'Lft (anyk t'Gen) t'Gen of
      Right g -> set (split sp <> (k *> g))
      Left () -> throw $ ImplementationError "vrcHomologyGroupGen"
      
  where
    k     = vrck v
    t'Gen = generator $ finitePresentation gen $ vrcT' v
    
    anyk :: T (Free k) d -> Any k
    anyk (SliceFrom (Free k) _) = k

--------------------------------------------------------------------------------
-- vrcBoundary -

-- | evaluates the boundary of a given chain.
vrcBoundary :: Distributive d => Variance i d -> S (i N1) d -> T (i N1) d
vrcBoundary v c = vrcC v *> c

--------------------------------------------------------------------------------
-- vrcBoundary' -

-- | tries to evaluates the boundary' of a given chain.
--
--  __Property__ Let @v@ be in @'Variance' __i__ __c__@ and @s@ in @'S' __i__ __c__@ with
--  @end s == start c@ (see diagram in 'Variance'), then holds:
--
--  (1) If @t = c *> s@ is not zero, then the result is @'Left' ('Left' t)@, otherwise
--
--  (2) Let @s'@ be the factor with @end s' = start c'@. If @t' = c' *> s'@ is not zero, then the
--  result is @'Left' ('Right' t')@, otherwise
--
--  (3) The result is @'Right' r@ such that @b *> r == s@,
vrcBoundary' :: Variance i d -> S (i N1) d -> Either (Either (T (i N1) d) (T' (i N1) d)) (R (i N1) d)
vrcBoundary' (Variance _ cKerUnv c'KerUnv b''Lft _) s
  = case cKerUnv s of
      Left t      -> Left (Left t)
      Right s'    -> case c'KerUnv s' of
        Left t'   -> Left (Right t')
        Right s'' -> Right (b''Lft s'')

--------------------------------------------------------------------------------
-- VarianceTrafo -

-- | transformation between variances.
--
-- @
--                v b            v c
--   v :    v r --------> v s ----------> v t
--   |       |            |                |
--   | t     |            |                |
--   |       |            |                | 
--   v       v            v                v
--   w :    w r --------> w s------------> w t
--                w b            w c
--
-- @
--
-- __Property__ Let @t@ be in @'Variance' __i__ __d__@ for a 'Distributive' structure @__d__@, then
-- holds: @'vrtTop' t@ is 'valid'. 
data VarianceTrafo i d
  = VarianceTrafo (Variance i d) (Variance i d) (FinList N3 d)

--------------------------------------------------------------------------------
-- vrtTop -

-- | the underlying transformation between the two top chain complexes.
vrtTop :: VarianceTrafo i d -> ChainComplexTrafo From N0 d
vrtTop (VarianceTrafo (Variance v3x3 _ _ _ _) (Variance w3x3 _ _ _ _) t) = ChainComplexTrafo top where
  top = Transformation v w t

  DiagramChainTo v _ = v3x3
  DiagramChainTo w _ = w3x3

--------------------------------------------------------------------------------
-- VarianceTrafo - Validable -

instance Distributive d => Validable (VarianceTrafo i d) where
  valid t = Label "VarianceTrafo" :<=>: (valid $ vrtTop t)

--------------------------------------------------------------------------------
-- vrtCenter -

-- | the induced transformation betweenthe two center chain complexes.
vrtCenter :: Multiplicative d => VarianceTrafo i d -> ChainComplexTrafo From N0 d
vrtCenter v@(VarianceTrafo (Variance v3x3 _ _ _ _) w@(Variance w3x3 _ _ _ _) (t0:|t1:|t2:|Nil))
  = ChainComplexTrafo center where
  
  center = Transformation v' w' (t'0:|t'1:|t'2:|Nil)

  DiagramChainTo _ (vu:|_) = v3x3
  DiagramChainTo _ (wu:|_) = w3x3

  v' = start vu
  w' = start wu
  
  t'0 = t0
  t'1 = error "nyi"
  t'2 = error "nyi"
  
--------------------------------------------------------------------------------
-- Variance' -

-- | restricted variance (see also 'Variance').
--
-- @
--                  b            c
--   p :     r ---------> s -------------> t
--   ^       ^            ^                ^
--   |       |            |                |
--   | u     | one        | k = ker c      | 0
--   |       |            |                |
--   p':     r ---------> s'------------>> t'
--                b'         c' = coker b'
-- @
data Variance' i d where
  Variance'
   :: Transformation (Chain From) N3 N2 d
   -> (S (i N1) d -> Either (T (i N1) d) (S' (i N1) d))
   
      -- | the liftable property of @c'@.
    -> (forall (k :: N') . Sliced (i k) d => Any k -> T' (i k) d -> Either () (S' (i k) d))
   -> Variance' i d

--------------------------------------------------------------------------------
-- ccxVariance' -

-- in a further release the constraint (i ~ Free) can be relaxed by adapting CokernlLiftableFree
-- and Generator!

-- | evaluates the restricted varaince of the first two arrows..
--
-- @
--                  b            c
--   p :     r ---------> s -------------> t
--   ^       ^            ^                ^
--   |       |            |                |
--   | u     | one        | k = ker c      | 0
--   |       |            |                |
--   p':     r ---------> s'------------>> t'
--                b'         c' = coker b'
-- @
ccxVariance' :: (Distributive d, i ~ Free)
  => Kernels N1 d -> ClfCokernels N1 d
  -> ChainComplex From l d
  -> Variance' i d
ccxVariance' kers cokers (ChainComplex (DiagramChainFrom r (b:|c:|_)))
  = Variance' u kUniv (lft c' (clfLiftableFree b'CokerLft)) where
      
  u  = Transformation p' p (one r :| k :| zero (end c' :> end c) :| Nil)
  p  = DiagramChainFrom r (b :|c :|Nil)
  p' = DiagramChainFrom r (b':|c':|Nil) 


  cDgm = kernelDiagram c
  cKer = limes kers cDgm
  k    = kernelFactor $ universalCone cKer

  b'   = universalFactor cKer (ConeKernel cDgm b)
  

  b'Dgm      = cokernelDiagram b'
  b'CokerLft = clfLimes cokers b'Dgm
  b'Coker    = clfCokernel b'CokerLft
  c'         = cokernelFactor $ universalCone b'Coker
  
  kUniv s@(SliceFrom i s')
    | not $ isZero $ slice t = Left t
    | otherwise              = Right (SliceFrom i $ universalFactor cKer $ ConeKernel cDgm s')
    where t = c *> s
    
  lft :: (Oriented d, Sliced (i k) d) => d -> (Any k -> Liftable From (i k) d)
        -> Any k -> T' (i k) d -> Either () (S' (i k) d)
  lft c' l k s
    | end s /= end c' = Left ()
    | otherwise       = Right $ lift (l k) s


--------------------------------------------------------------------------------
-- ccxZFromVariance -

-- | evaluates the 'Variance' of the first two matrices where they are mapped in to 'AbHom'
-- via 'FreeAbHom'.    
ccxZFromVariance :: ChainComplex From l (Matrix Z) -> Variance Free AbHom
ccxZFromVariance ccx = Variance d3x3 kUniv k'Univ b''Lft c'Lft where
    p = ccxMap FreeAbHom ccx

    vrcZ = ccxVariance' abhKernels abhCokersLftFree

    Variance' u kUniv c'Lft = vrcZ p
    Variance' u' k'Univ _   = vrcZ (ChainComplex $ start u)
      
    d3x3 = DiagramChainTo (end u) (u:|u':|Nil)
    
    b''  = head $ dgArrows $ start u'
    b''Z = abhz b''
    
    -- see the note of Variance
    b''Lft :: S (Free k) AbHom -> R (Free k) AbHom
    b''Lft (SliceFrom k s'') = SliceFrom k (zabh rZ) where
      s''Z = abhz s''
      rZ = case zMatrixLift b''Z s''Z of
        Just x  -> x 
        Nothing -> throw $ ImplementationError "zMatrixLift dos not hold spezification"

--------------------------------------------------------------------------------
-- ccxZToVariance -

-- | evaluates the 'Variance' of the first two matrices where they are mapped in to 'AbHom'
-- via 'FreeAbHom'.    
ccxZToVariance :: ChainComplex To l (Matrix Z) -> Variance Free AbHom
ccxZToVariance (ChainComplex (DiagramChainTo _ (f:|f':|_))) = ccxZFromVariance ccx where
  ccx = ChainComplex (DiagramChainFrom (start f') (f':|f:|Nil))

--------------------------------------------------------------------------------
-- ccxZToVariances -

ccxZToVariances :: ChainComplex To l (Matrix Z) -> FinList (l+1) (Variance Free AbHom)
ccxZToVariances = vrcs where
  vrcs :: ChainComplex To l (Matrix Z) -> FinList (l+1) (Variance Free AbHom)
  vrcs c = ccxZToVariance c :| case c of
    ChainComplex (DiagramChainTo _ (_:|_:|Nil))  -> Nil
    ChainComplex (DiagramChainTo _ (_:|_:|_:|_)) -> vrcs (ccxTail c)
    
a = complex [Set "abc"]
b = complex [Set [0,1]] :: Complex N

c = cpxProductAsc b a

p1 = ComplexMapAsc c b (Map fst)
p2 = ComplexMapAsc c a (Map snd)

c' = cpxProduct b a

p1' = ComplexMap c b (Map fst)
p2' = ComplexMap c a (Map snd)

hmg :: (Entity x, Ord x, Simplical s x) => (ChainComplexRep Z s n x -> ChainComplex To n (Matrix Z))
  -> Regular -> Any n -> Complex x -> FinList (n+1) AbGroup
hmg rep r n c = amap1 vrcT' $ ccxZToVariances $ rep $ chainComplexRep r n c

hmgSet :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> FinList (n+1) AbGroup
hmgSet = hmg chainComplexSet

hmgAsc :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> FinList (n+1) AbGroup
hmgAsc = hmg chainComplexAsc

hmgLst :: (Entity x, Ord x) => Regular -> Any n -> Complex x -> FinList (n+1) AbGroup
hmgLst = hmg chainComplexLst

chainComplexSet :: (Ring r, Commutative r, Entity x, Ord x)
  => ChainComplexRep r Set n x -> ChainComplex To n (Matrix r)
chainComplexSet = chainComplex

chainComplexAsc :: (Ring r, Commutative r, Entity x, Ord x)
  => ChainComplexRep r Asc n x -> ChainComplex To n (Matrix r)
chainComplexAsc = chainComplex

chainComplexLst :: (Ring r, Commutative r, Entity x, Ord x)
  => ChainComplexRep r [] n x -> ChainComplex To n (Matrix r)
chainComplexLst = chainComplex
