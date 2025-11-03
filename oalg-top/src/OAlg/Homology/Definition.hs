
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}

-- |
-- Module      : OAlg.Homology.Definition
-- Description : homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- homology.
module OAlg.Homology.Definition
  (

    -- * Homology
    homology, Homology
  , homologyGroups
  , hmgCycles, hmgClassGenerators
  , abhCnzf, abhCnzfHomology

  , homologyClass, boundary, boundaryInv
    
    -- * Homomorphism
  , homologyHom, HomologyHom
  , homologyGroupsHom
  , abhCnzfh, abhCnzfhHomologyHom

  , ConsecutiveZeroFreeHom(..)

  ) where

import Control.Monad

import Data.Typeable

import Data.Foldable (toList)
import Data.List as L (zip,filter, (++))

import OAlg.Prelude

import OAlg.Data.FinitelyPresentable

import OAlg.Structure.Exception
import OAlg.Structure.Oriented
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative
import OAlg.Structure.Exponential
import OAlg.Structure.Distributive
import OAlg.Structure.Operational

import OAlg.Entity.Diagram as D 
import OAlg.Entity.Natural
import OAlg.Entity.FinList as F
import OAlg.Entity.Slice
import OAlg.Entity.Slice.Liftable
import OAlg.Entity.Matrix
import OAlg.Entity.Sequence.PSequence

import OAlg.Hom.Distributive

import OAlg.AbelianGroup.Definition
import OAlg.AbelianGroup.KernelsAndCokernels
import OAlg.AbelianGroup.Liftable
import OAlg.AbelianGroup.ZMod hiding (NotEligible)

import OAlg.Limes.Definition
import OAlg.Limes.Cone
import OAlg.Limes.KernelsAndCokernels
import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
import OAlg.Limes.Exact.Free

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex

import OAlg.Homology.Eval.Core

import OAlg.Adjunction.Definition

--------------------------------------------------------------------------------
-- cnzfDiagram -

cnzfDiagram :: ConsecutiveZeroFree t n x -> Diagram (Chain t) (n+3) (n+2) x
cnzfDiagram (ConsecutiveZeroFree d _) = cnzDiagram d

--------------------------------------------------------------------------------
-- ConsecutiveZeroFreeHom -

data ConsecutiveZeroFreeHom t n x where
  ConsecutiveZeroFreeHom :: ConsecutiveZeroFree t n x -> ConsecutiveZeroFree t n x
    -> FinList (n+3) x -> ConsecutiveZeroFreeHom t n x

deriving instance (Show x, ShowPoint x) => Show (ConsecutiveZeroFreeHom t n x)
deriving instance (Eq x, EqPoint x) => Eq (ConsecutiveZeroFreeHom t n x)

instance Distributive x => Validable (ConsecutiveZeroFreeHom t n x) where
  valid (ConsecutiveZeroFreeHom a b fs) = Label "ConsecutiveZeroFreeHom" :<=>:
    And [ valid a
        , valid b
        , vldCm 0 (dgArrows $ cnzfDiagram a) (dgArrows $ cnzfDiagram b) fs
        ] where

    vldCm :: Multiplicative x => N -> FinList n x -> FinList n x -> FinList (n+1) x -> Statement
    vldCm _ Nil _ _ = SValid
    vldCm i (a:|as) (b:|bs) (f:|f':|fs)
      = (f * a == b * f') :?> Params ["i":=show i] && vldCm (succ i) as bs (f':|fs)

--------------------------------------------------------------------------------
-- Distributive -

type instance Point (ConsecutiveZeroFreeHom t n x) = ConsecutiveZeroFree t n x

instance (Show x, ShowPoint x) => ShowPoint (ConsecutiveZeroFreeHom t n x)
instance (Eq x, EqPoint x) => EqPoint (ConsecutiveZeroFreeHom t n x)
instance Distributive x => ValidablePoint (ConsecutiveZeroFreeHom t n x)
instance (Typeable t, Typeable n, Typeable x) => TypeablePoint (ConsecutiveZeroFreeHom t n x)

instance (Distributive x, Typeable t, Typeable n) => Oriented (ConsecutiveZeroFreeHom t n x) where
  orientation (ConsecutiveZeroFreeHom a b _) = a :> b

instance (Distributive x, Typeable t, Typeable n)
  => Multiplicative (ConsecutiveZeroFreeHom t n x) where
  one a = ConsecutiveZeroFreeHom a a (amap1 one $ dgPoints $ cnzfDiagram a)

  ConsecutiveZeroFreeHom b' c fs * ConsecutiveZeroFreeHom a b gs
    | b' /= b   = throw NotMultiplicable
    | otherwise = ConsecutiveZeroFreeHom a c (amap1 (uncurry (*)) (fs `F.zip` gs))
    

--------------------------------------------------------------------------------
-- Homology -

-- | homology.
type Homology n = VarianceFreeLiftable To n AbHom

--------------------------------------------------------------------------------
-- abhCnzf -

abhCnzf :: Simplical s x => ChainComplex t Z s n x -> ConsecutiveZeroFree To n AbHom
abhCnzf = toFree . ccxRepMatrix where
  
  toFree :: ConsecutiveZero To n (Matrix Z) -> ConsecutiveZeroFree To n AbHom
  toFree ds = ConsecutiveZeroFree ds' fs where
    ds' = cnzMapCov (homDisjOpDst FreeAbHom) ds
    fs  = amap1 (fromJust . abgSomeFree) $ tail $ dgPoints $ cnzDiagram ds'

--------------------------------------------------------------------------------
-- abhCnzfHomology -

abhCnzfHomology :: ConsecutiveZeroFree To n AbHom -> Homology n
abhCnzfHomology = varianceFreeTo abhKernelsSomeFreeFreeTip abhCokernelsLiftableSomeFree

--------------------------------------------------------------------------------
-- homology -

-- | the induced homology of a complex.
homology :: Simplical s x => ChainComplex t Z s n x -> Homology n
homology = abhCnzfHomology . abhCnzf

--------------------------------------------------------------------------------
-- homologyGroups -

-- | the homology groups.
homologyGroups :: Attestable n => Homology n -> Deviation (n+1) AbHom
homologyGroups = deviationsTo

--------------------------------------------------------------------------------
-- HomologyHom -

-- | homomorphism between homologies.
type HomologyHom n = VarianceFreeLiftableHom To n AbHom

--------------------------------------------------------------------------------
-- abhCnzfh -

abhCnzfh :: Homological s x y => ChainComplexHom t Z s n x y -> ConsecutiveZeroFreeHom To n AbHom
abhCnzfh h@(ChainComplexHom a b _) = ConsecutiveZeroFreeHom a' b' fs' where
  a'  = abhCnzf a
  b'  = abhCnzf b
  ConsecutiveZeroHom (DiagramTrafo _ _ ts) = ccxRepMatrixHom h
  fs' = amap1 (amap FreeAbHom) ts

--------------------------------------------------------------------------------
-- cnzfhHomologyHom -

abhCnzfhHomologyHom :: ConsecutiveZeroFreeHom To n AbHom -> HomologyHom n
abhCnzfhHomologyHom (ConsecutiveZeroFreeHom a b fs) = VarianceHomG a' b' fs where
  a' = abhCnzfHomology a
  b' = abhCnzfHomology b

--------------------------------------------------------------------------------
-- homologyHom -

-- | the induced homomorphism between homologies.
homologyHom :: Homological s x y => ChainComplexHom t Z s n x y -> HomologyHom n
homologyHom = abhCnzfhHomologyHom . abhCnzfh

--------------------------------------------------------------------------------
-- hmgGroupsHom -

-- | homomorphism between the homology groups.
homologyGroupsHom :: Attestable n => HomologyHom n -> DeviationHom (n+1) AbHom
homologyGroupsHom = deviationHomG (Struct :: Struct (Dst,SldFr) AbHom)

--------------------------------------------------------------------------------
-- hmgCycles -

-- | list of cycles generating the sub group of cycles for the head homology.  
hmgCycles :: Homology n -> [AbElement]
hmgCycles (VarianceG _ ((ker,_):|_)) = case universalCone ker of
  ConicFreeTip _ cn -> amap1 (k*>) $ abges $ start k where k = kernelFactor cn

--------------------------------------------------------------------------------
-- hmgClassGenerators -

-- | list of cycles genrating the homology group for the head homology.
hmgClassGenerators :: Homology n -> [AbElement]
hmgClassGenerators (VarianceG _ ((ker,coker):|_))
  = case finitePresentation abgFinPres (tip $ cone cCn) of
      GeneratorTo (DiagramChainTo _ (g:|_)) k'@(Free a) _ _ _ _
        -> toList $ amap1 AbElement $ split abhSplitable $ (k*>)
         $ lift (liftFree cLft a) (SliceFrom k' g)
  where
    ConeCokernelLiftable cCn cLft = universalCone coker
    k = kernelFactor $ universalCone ker

--------------------------------------------------------------------------------
-- hmgBoundaryOperator -

-- | the boundary operators of the head homology.
hmgBoundaryOperator :: Homology n -> ConsecutiveZero To N0 AbHom
hmgBoundaryOperator (VarianceG cs _) = cnzHead cs

--------------------------------------------------------------------------------
-- hmgChain -

-- | the abelian group of chains for the head homology.
hmgChain :: Homology n -> AbGroup
hmgChain (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) = start d

--------------------------------------------------------------------------------
-- homologyClass -

-- | the homology class of a cycle in the head homology.
homologyClass :: Homology n -> AbElement -> Eval AbElement
homologyClass (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) ((ker,coker):|_)) e
  | start d /= end e      = failure $ NotEligible "homologyClass"
  | not (isZero (d *> e)) = failure $ NotCycle "homologyClass"
  | otherwise = return (c *> e')

  where
    AbElement (SliceFrom k1 eh) = e
    c   = cokernelFactor $ universalCone coker
    eh' = universalFactor ker (ConeKernel (universalDiagram ker) eh)
    e'  = AbElement (SliceFrom k1 eh')

--------------------------------------------------------------------------------
-- boundary -

-- | the boundary of an abelian element.
boundary :: Homology n -> AbElement -> Eval AbElement
boundary (VarianceG (ConsecutiveZero (DiagramChainTo _ (d:|_))) _) e
  | start d /= end e  = failure $ NotEligible "boundary"
  | otherwise         = return (d *> e)

--------------------------------------------------------------------------------
-- abhFreeEmbedding -

-- | the canonical emmedding of the free part of a given abelian group.
--
-- __Property__ Let @'Adjunction' l r u v = 'abhFreeAdjunction'@, @rl = 'pmap' r '.' 'pmap' l@
-- and @i = 'abhFreeEmbedding'@, then holds:
--
-- (1) For all @g@ in 'AbGroup' holds: @u g v'*' i g@ is 'one'. (see diagram belaow)
--
-- @
--                 l
--             <--------- 
--    Matrix Z            AbHom
--             --------->
--                 r
--                               u g
--                           ----------->
--                         g              rl g = pmap r (pmap l g)
--                           <-----------
--                               i g
-- @
--
-- __Note__ If @g@ is free, then @'abgFreeEmbedding' g@ is 'one'.
abhFreeEmbedding :: AbGroup -> AbHom
abhFreeEmbedding g = AbHom $ Matrix (abgDim g) (abgDim rlg) $ Entries $ PSequence $ oijs where
  rlg  = pmap FreeAbHom (pmap AbHomFree g)
  oijs = amap1 oij $ ((filter gFree $ abgxs g) `L.zip` [0..]) 

  gFree :: (ZMod,N) -> Bool
  gFree (ZMod n,_) = n == 0

  oij :: ((ZMod,N),N) -> (ZModHom,(N,N))
  oij ((z,i),j) = (one z,(i,j))

--------------------------------------------------------------------------------
-- prpAbhFreeEmbedding -

-- | validity according to 'abhFreeEmbedding'.
prpAbhFreeEmbedding :: AbGroup -> Statement
prpAbhFreeEmbedding g = Prp "AbhFreeEmbedding"
  :<=>: (u g * i == one (start i)) :?> Params ["g":= show g] where
  
  Adjunction _ _ u _ = abhFreeAdjunction
  i                  = abhFreeEmbedding g
  
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
    asp (a:>b,mf) = [abhTrv $ slice a, abhTrv $ slice b] L.++ case mf of
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
-- boundaryInv -

-- | determines the bounary of a given cycle with zero homology class.
boundaryInv :: Homology n -> AbElement -> Eval AbElement
boundaryInv hmg e = do
  h <- homologyClass hmg e
  case isZero h of
    True               -> case universalCone ker of
      ConicFreeTip k _ -> case abhLift (SliceTo k e'' :> SliceTo k d'') of
        Just e'''      -> return $ AbElement $ SliceFrom k1 $ slfFactor e'''
        Nothing        -> failure $ EvalFailure "implementation error!"
                          -- as h is zero, e' should be liftable!
    False -> failure $ NonZeroHomologyClass h

  where
    VarianceG (ConsecutiveZero (DiagramChainTo _ (_:|d':|_))) ((ker,_):|_) = hmg
    AbElement e'   = e
    SliceFrom k1 _ = e'

    e'' = universalFactor ker (ConeKernel (universalDiagram ker) (slice e'))
    d'' = universalFactor ker (ConeKernel (universalDiagram ker) d')

    
