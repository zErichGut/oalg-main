
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE TupleSections #-}

-- |
-- Module      : OAlg.Homology.Eval.Definition
-- Description : evaluations for homology.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- evaluations for homology.
module OAlg.Homology.Eval.Definition
  (
  ) where

import Control.Monad 

import Data.Typeable
import Data.Kind
import Data.Foldable (toList)
import Data.Array
import Data.List as L (zip,(++),foldl)
import qualified Data.Map as M

import OAlg.Prelude

import OAlg.Category.Path

import OAlg.Data.Proxy
-- import OAlg.Data.Either
-- import OAlg.Data.Reducible
import OAlg.Data.Constructable
import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.FibredOriented
import OAlg.Structure.Additive
-- import OAlg.Structure.Distributive
-- import OAlg.Structure.Exponential

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural hiding (S)
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sum
-- import OAlg.Entity.Slice.Free
import OAlg.Entity.Matrix

import OAlg.Hom.Definition

import OAlg.AbelianGroup.Definition
-- import OAlg.AbelianGroup.KernelsAndCokernels

-- import OAlg.Limes.Exact.ConsecutiveZero
import OAlg.Limes.Exact.Deviation
-- import OAlg.Limes.Exact.Free

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator hiding (Boundary,boundary)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition
import OAlg.Homology.Eval.Core

--------------------------------------------------------------------------------

instance Ix i => ApplicativeG (Array i) (->) (->) where amapG = fmap

--------------------------------------------------------------------------------
-- ChainType -

-- | types of chains
data ChainType
  = GeneralType  -- ^ general chains with no restriction.
  | CycleType    -- ^ chains with zero boundary.
  | HomologyType -- ^ cycles with non zero homology classes.
  deriving (Show,Eq,Ord,Enum,Bounded,Ix)

--------------------------------------------------------------------------------
-- ChainValue -

type ChainValue s x = ChainG Z s x

--------------------------------------------------------------------------------
-- ChainList -

type ChainList s x = Array Z (ChainValue s x)

--------------------------------------------------------------------------------
-- SomeChainComplex -

-- | ignoring the 'ChainComplexType'.
data SomeChainComplex r s n x where
  SomeChainComplex ::  ChainComplex t r s n x -> SomeChainComplex r s n x

--------------------------------------------------------------------------------
-- Env -

-- | environment for evaluations in the context of homologies.
--
-- __Prperty__ Let @env@ be in @t'Env' __t s n x__@, then holds:
--
-- (1) Let @chs = 'envChains' env@, @n@ in 'Z' and let @C@ denote the free abelian group, generated
-- by the set of simplices @'envSimplexSet' env n@, then holds:
--
--     (1) @chs 'GeneralType' n@ is the canonical base in @C@ given by @'envSimplexSet' env n@.
--
--     (2) @chs 'CycleType' n@ is a base for the cycles in @C@.
--
--     (3) @chs 'HomologyType' n@ are cyles in @C@, generating the homology group at @n@.
data Env t s n x where
  Env :: (Simplical s x, Attestable n)
    => { envMaxDim       :: Z
       , envChainComplex :: ChainComplex t Z s n x
       , envHomology     :: Homology n
       , envAt           :: Array Z (SomeChainComplex Z s N0 x, Homology N0)
       , envSimplexSets  :: Array Z (Set (s x))     
       , envChains       :: Array ChainType (Array Z (ChainList s x))
       }
    -> Env t s n x

--------------------------------------------------------------------------------
-- env -

env :: (Simplical s x, Attestable n) => ChainComplexType t -> Any n -> Complex x -> Env t s n x
env t n c = case ats n of
  Ats -> Env { envMaxDim       = dm
             , envChainComplex = ccx
             , envHomology     = hmg
             , envAt           = at
             , envSimplexSets  = smps
             , envChains       = chs
             } where
    
    dm   = inj (lengthN n)
    ccx  = chainComplex t n c
    hmg  = homology ccx
    ats  = ccxhmg n ccx hmg
    
    smps = array (-1,dm+1) ([-1..] `L.zip` (toList $ dgPoints $ ccxDiagram ccx))
    at   = array (0,dm) ([0..] `L.zip` toList ats)
    cys  = array (0,dm) ([0..] `L.zip` (toList $ amap1 cycles ats))
    hms  = array (0,dm) ([0..] `L.zip` (toList $ amap1 homologies ats))

    chs  = array (GeneralType,HomologyType)
             [ (GeneralType, amap1 base smps)
             , (CycleType, cys)
             , (HomologyType, hms)
             ]

    base :: Simplical s x => Set (s x) -> Array Z (ChainValue s x)
    base (Set sxs) = array (0,n-1) ([0..] `L.zip` (amap1 ch sxs)) where n = inj (lengthN sxs)
    
    ccxhmg :: Simplical s x
      => Any n -> ChainComplex t Z s n x -> Homology n
      -> FinList (n+1) (SomeChainComplex Z s N0 x,Homology N0)
    ccxhmg n cc hm = (SomeChainComplex $ ccxHead cc,vrcHead hm) :| case n of
      W0    -> Nil
      SW n' -> ccxhmg n' (ccxTail cc) (vrcTail hm)

    -- mapping the elements to list of chains.
    toChnVls :: Simplical s x => SomeChainComplex Z s N0 x -> [AbElement] -> ChainList s x
    toChnVls (SomeChainComplex ccx) es
      = array (0,pred n) $ L.zip [0..] $ amap1 (cfsssy ssx . abgevec) $ es where

      ChainComplex _ (DiagramChainTo _ (d:|_)) = ccx
      ssx = start d
      n   = inj (lengthN es)

    -- base for the cycles.
    cycles :: Simplical s x => (SomeChainComplex Z s N0 x,Homology N0) -> ChainList s x
    cycles (sccx,hmg) = toChnVls sccx $ hmgCycles hmg

    -- generator for the homology classes as chains
    homologies :: Simplical s x => (SomeChainComplex Z s N0 x,Homology N0) -> ChainList s x
    homologies (sccx,hmg) = toChnVls sccx $ hmgClassGenerators hmg


env' :: (Simplical s x, Attestable n) => q s -> ChainComplexType t -> Any n -> Complex x -> Env t s n x
env' _ = env

t = ChainComplexStandard
n = attest :: Any N6
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N
s = Proxy :: Proxy Asc

ea = env' s t n a
eb = env' s t n b

--------------------------------------------------------------------------------
-- evalElmAt -

evalElmAt :: (Ix i, Show i) => Array i x -> i -> Eval x
evalElmAt xs i = if (bounds xs `inRange` i)
  then return (xs ! i)
  else failure $ IndexOutOfRange $ show i

--------------------------------------------------------------------------------
-- evalAt -

evalAt :: Env t s n x -> Z -> Eval (SomeChainComplex Z s N0 x,Homology N0)
evalAt env at = evalElmAt (envAt env) at 

--------------------------------------------------------------------------------
-- evalSimplexSet -

-- | evaluates the simplex set according to the given environment @enf@ and the given index
-- in the range @-1,0..n'+'1@ where @n = 'envMaxDim' env@. If the givne index is not in the
-- defined range then the evaluation yields a 'IndexOutOfRange' 'failure'.
evalSimplexSet :: Env t s n x -> Z -> Eval (Set (s x))
evalSimplexSet env@Env{} at = evalElmAt (envSimplexSets env) at 

--------------------------------------------------------------------------------
-- evalToAbElement -

-- | converting to the corresponding abelien element.
evalToAbElement :: Env t s n x -> Z -> ChainValue s x -> Eval AbElement
evalToAbElement env@Env{} at e = do
  ssx <- evalSimplexSet env at
  toAbElm ssx e

  where
    toAbElm :: Simplical s x => Set (s x) -> ChainValue s x -> Eval AbElement
    toAbElm ssx ch
      | ch' /= ch = failure $ NotEligible "evalToAbElement"
      | otherwise = return e
      where cfs = ssycfs ssx ch
            ch' = cfsssy ssx cfs
            e   = AbElement $ vecabhFree1 n cfs
            n   = lengthN ssx
    
--------------------------------------------------------------------------------
-- evalFromAbElement -

-- | converting from the corresponding abelien element.
evalFromAbElement :: Env t s n x -> Z -> AbElement -> Eval (ChainValue s x)
evalFromAbElement env@Env{} at e = do
  ssx <- evalSimplexSet env at
  fromAbElm ssx e
  
  where
    fromAbElm :: Simplical s x => Set (s x) -> AbElement -> Eval (ChainValue s x)
    fromAbElm ssx (AbElement e)
      | e' /= e   = failure $ NotEligible "evalFromAbElment"
      | otherwise = return ch
      where cfs = abhvecFree1 e
            ch  = cfsssy ssx cfs
            e'  = vecabhFree1 n cfs
            n   = lengthN (end e)
    

--------------------------------------------------------------------------------
-- evalChainsAt -

evalChainsAt :: Env t s n x -> ChainType -> Z -> Eval (ChainList s x)
evalChainsAt env t at = do
  chs <- evalElmAt (envChains env) t
  evalElmAt chs at

--------------------------------------------------------------------------------
-- evalChainAt -

evalChainAt :: Env t s n x -> ChainType -> Z -> Z -> Eval (ChainValue s x)
evalChainAt env t at i = do
  chsAt <- evalChainsAt env t at
  evalElmAt chsAt i

--------------------------------------------------------------------------------
-- evalCardSmpSetAll -

evalCardSmpSetAll :: Env t s n x -> Cards Z n
evalCardSmpSetAll env@Env{} = ccxCards $ envChainComplex env

--------------------------------------------------------------------------------
-- evalCardSmpSetAt ´-

evalCardSmpSetAt :: Env t s n x -> Z -> Eval (Cards Z N0)
evalCardSmpSetAt env@Env{} i = do
  SomeChainComplex ccx <- evalAt env i >>= return . fst
  return $ ccxCards ccx

--------------------------------------------------------------------------------
-- evalHmgGroupAll -

evalHmgGroupAll :: Env t s n x -> Deviation (n+1) AbHom
evalHmgGroupAll env@Env{} = homologyGroups $ envHomology env

--------------------------------------------------------------------------------
-- evalHmgGroupAt -

evalHmgGroupAt :: Env t s n x -> Z -> Eval (Deviation N1 AbHom)
evalHmgGroupAt env i = evalAt env i >>= return . homologyGroups . snd

--------------------------------------------------------------------------------
-- evalBoundaryAt -

evalBoundaryAt :: Env t s n x -> Z -> ChainValue s x -> Eval (ChainValue s x)
evalBoundaryAt env at ch = do
  e  <- evalToAbElement env at ch
  h  <- evalAt env at >>= return . snd
  e' <- boundary h e
  evalFromAbElement env (pred at) e'

--------------------------------------------------------------------------------
-- Vec -

data Vec x = Vec (Root x) (PSequence Z x)

deriving instance Fibred x => Show (Vec x)
deriving instance Fibred x => Eq (Vec x)
deriving instance (Fibred x, Ord x, OrdRoot x) => Ord (Vec x)

instance Additive x => Validable (Vec x) where
  valid (Vec r xs) = Label "Vec" :<=>:
    And [ valid xs
        , foldl (vld r) SValid (amap1 fst $ psqxs xs)
        ] where

    vld :: Additive x => Root x -> Statement -> x -> Statement
    vld r s x = And [ s
                    , Label "Root" :<=>: (root x == r) :?> Params ["r":=show r,"x":=show x]
                    , Label "non Zero" :<=>: not (isZero x) :?> Params ["x":=show x]
                    ]


type instance Root (Vec x) = Root x
instance Fibred x => ShowRoot (Vec x)
instance Fibred x => EqRoot (Vec x)
instance Fibred x => ValidableRoot (Vec x)
instance Fibred x => TypeableRoot (Vec x)

instance Additive x => Fibred (Vec x) where
  root (Vec r _) = r

instance Additive x => Additive (Vec x) where
  zero r = Vec r psqEmpty

  Vec r a + Vec r' b | r == r'   = Vec r (psqFilter (not . isZero) $ psqInterlace (+) id id a b)
                     | otherwise = throw NotAddable

  ntimes n (Vec r xs) = Vec r (psqFilter (not . isZero) $ psqMap (ntimes n) xs)

instance Abelian x => Abelian (Vec x) where
  negate (Vec r xs) = Vec r (psqMap negate xs)

  Vec r a - Vec r' b | r == r'   = Vec r (psqFilter (not . isZero) $ psqInterlace (-) id id a b)
                     | otherwise = throw NotAddable

  ztimes z (Vec r xs) = Vec r (psqFilter (not . isZero) $ psqMap (ztimes z) xs)

--------------------------------------------------------------------------------
-- ChainValueVec -

data ChainValueAt s x = ChainValueAt Z (ChainValue s x) deriving (Show,Eq,Ord)

instance Simplical s x => Validable (ChainValueAt s x) where
  valid (ChainValueAt d xs) = Label "ChainValueAt" :<=>:
    And [ valid xs
        , foldl (vld d) SValid (amap1 snd $ lcs $ ssylc xs)
        ] where

    vld :: Simplical s x => Z -> Statement -> s x -> Statement
    vld d s sx = And [ s
                     , Label "dim" :<=>: (d == dimension sx) :?> Params ["d":=show d, "sx":=show sx]
                     ]

type instance Root (ChainValueAt s x) = Z
instance ShowRoot (ChainValueAt s x)
instance EqRoot (ChainValueAt s x)
instance OrdRoot (ChainValueAt s x)
instance ValidableRoot (ChainValueAt s x)
instance TypeableRoot (ChainValueAt s x)

instance Simplical s x => Fibred (ChainValueAt s x) where
  root (ChainValueAt d _) = d

instance Simplical s x => Additive (ChainValueAt s x) where
  zero d = ChainValueAt d (zero ())

  ChainValueAt d a + ChainValueAt d' b | d == d'   = ChainValueAt d (a+b)
                                       | otherwise = throw NotAddable

  ntimes n (ChainValueAt d sx) = ChainValueAt d (ntimes n sx)

instance Simplical s x => Abelian (ChainValueAt s x) where
  negate (ChainValueAt d sx) = ChainValueAt d (negate sx)

  ChainValueAt d a - ChainValueAt d' b | d == d'   = ChainValueAt d (a-b)
                                       | otherwise = throw NotAddable
  
  ztimes z (ChainValueAt d sx) = ChainValueAt d (ztimes z sx)


--------------------------------------------------------------------------------
-- evalChainValuesAt

evalChainsVecAt :: Env t s n x -> ChainType -> Z -> Eval (Vec (ChainValueAt s x))
evalChainsVecAt env@Env{} t at = do
  chs <- evalChainsAt env t at
  return $ Vec at
         $ psqFilter (not . isZero)
         $ PSequence
         $ amap1 (\(i,c) -> (ChainValueAt at c,i))
         $ assocs chs

--------------------------------------------------------------------------------
-- evalChainVecAt -

evalChainVecAt :: Env t s n x -> ChainType -> Z -> Z -> Eval (Vec (ChainValueAt s x))
evalChainVecAt env@Env{} t at i = do
  ch <- evalChainAt env t at i
  return $ Vec at
         $ psqFilter (not . isZero)
         $ PSequence
         $ [(ChainValueAt at ch,0)]

--------------------------------------------------------------------------------
-- psqSequence -

psqSequence :: Monad m => PSequence i (m x) -> m (PSequence i x)
psqSequence (PSequence xis) = (sequence $ amap1 mxi xis) >>=  return . PSequence where
  
  mxi :: Monad m => (m x,i) -> m (x,i)
  mxi (mx,i) = mx >>= return . (,i)

--------------------------------------------------------------------------------
-- evalBoundaryChainValueAt -

evalBoundaryChainValueAt :: Env t s n x -> ChainValueAt s x -> Eval (ChainValueAt s x)
evalBoundaryChainValueAt env (ChainValueAt at ch)
  = evalBoundaryAt env at ch >>= return . ChainValueAt (pred at)

--------------------------------------------------------------------------------
-- evalBoundaryVec -

evalBoundaryVec :: Env t s n x -> Vec (ChainValueAt s x) -> Eval (Vec (ChainValueAt s x))
evalBoundaryVec env@Env{} (Vec at chs) = do
  chs' <- psqSequence $ psqMap (evalBoundaryChainValueAt env) chs
  return (Vec (pred at) (psqFilter (not . isZero) chs'))


{-
--------------------------------------------------------------------------------
-- evalHomologyClassAt -

evalHomologyClassAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval AbElement
evalHomologyClassAt env vrs at vexpr = do
  c <- evalChainValueAt env vrs at vexpr
  e  <- evalToAbElement env (inj at) c
  h  <- evalAt env at >>= return . snd
  homologyClass h e
-}

--------------------------------------------------------------------------------
-- AbelianExpressionType -

data AbelianExpressionType v s x where
  AblExprTypeVoid     :: AbelianExpressionType () s x
  AblExprTypeZ        :: AbelianExpressionType Z s x
  AblExprTypeChain    :: AbelianExpressionType (Vec (ChainValueAt s x)) s x
  AblExprTypeHmgClass :: AbelianExpressionType (Vec AbElement) s x

--------------------------------------------------------------------------------
-- AbelianOperator -

data AbelianOperator v s x where
  AblOprChainAll :: ChainType -> AbelianOperator ((),Vec (ChainValueAt s x)) s x
  AblOprChainAt  :: ChainType -> AbelianOperator (Z,Vec (ChainValueAt s x)) s x
  AblOprBoundary :: AbelianOperator (Vec (ChainValueAt s x),Vec (ChainValueAt s x)) s x

deriving instance Simplical s x => Show (AbelianOperator v s x)

--------------------------------------------------------------------------------
-- AbelianExpression -

data AbelianExpression v s x where
  AblExprValue    :: AbelianValue v s x -> AbelianExpression v s x
  AblExprVariable :: String -> AbelianExpression v s x
  AblExprZero     :: AbelianValueType v s x -> AbelianExpression v s x
  (:!>)           :: AbelianExpression Z s x -> AbelianExpression v s x -> AbelianExpression v s x
  (:+:)           :: AbelianExpression v s x -> AbelianExpression v s x -> AbelianExpression v s x
  (:$:)           :: AbelianOperator (u,v) s x -> AbelianExpression u s x -> AbelianExpression v s x
  
deriving instance Simplical s x => Show (AbelianExpression v s x)

--------------------------------------------------------------------------------
-- AbelianValueType -

data AbelianValueType v s x where
  AblValTypeVoid     :: AbelianValueType () s x
  AblValTypeZ        :: AbelianValueType Z s x
  AblValTypeChain    :: Z -> AbelianValueType (Vec (ChainValueAt s x)) s x
  AblValTypeHmgClass :: AbGroup -> AbelianValueType (Vec AbElement) s x
  
deriving instance Show (AbelianValueType v s x)
deriving instance Eq (AbelianValueType v s x)

instance Validable (AbelianValueType v s x) where
  valid t = Label "AbelianValueType" :<=>: case t of
    AblValTypeVoid       -> SValid
    AblValTypeHmgClass g -> valid g
    AblValTypeChain z    -> valid z
    AblValTypeZ          -> SValid

--------------------------------------------------------------------------------
-- AbelianValue -

data AbelianValue v s x where
  ValVoid     :: AbelianValue () s x
  ValZ        :: Z -> AbelianValue Z s x
  ValChain    :: Vec (ChainValueAt s x) -> AbelianValue (Vec (ChainValueAt s x)) s x
  ValHmgClass :: Vec AbElement -> AbelianValue (Vec AbElement) s x 

deriving instance Simplical s x => Show (AbelianValue v s x)
deriving instance Simplical s x => Eq (AbelianValue v s x)

instance OrdRoot AbElement
deriving instance Simplical s x => Ord (AbelianValue v s x)

instance Simplical s x => Validable (AbelianValue v s x) where
  valid v = Label "AbelianValue" :<=>: case v of
    ValVoid        -> SValid
    ValZ z         -> valid z
    ValChain chs   -> valid chs
    ValHmgClass hs -> valid hs


type instance Root (AbelianValue v s x) = AbelianValueType v s x

deriving instance ShowRoot (AbelianValue v s x)
deriving instance EqRoot (AbelianValue v s x)
deriving instance ValidableRoot (AbelianValue v s x)
deriving instance (Typeable s, Typeable v, Typeable x) => TypeableRoot (AbelianValue v s x)

instance (Simplical s x, Typeable v) => Fibred (AbelianValue v s x) where
  root ValVoid          = AblValTypeVoid
  root (ValZ _)         = AblValTypeZ
  root (ValChain chs)   = AblValTypeChain (root chs)
  root (ValHmgClass hs) = AblValTypeHmgClass (root hs) 

instance (Simplical s x, Typeable v) => Additive (AbelianValue v s x) where
  zero AblValTypeVoid         = ValVoid
  zero AblValTypeZ            = ValZ (zero (():>()))
  zero (AblValTypeChain z)    = ValChain (zero z)
  zero (AblValTypeHmgClass g) = ValHmgClass (zero g)

  ValVoid + ValVoid             = ValVoid
  ValZ a + ValZ b               = ValZ (a+b)
  ValChain a + ValChain b       = ValChain (a+b)
  ValHmgClass h + ValHmgClass h'= ValHmgClass (h+h')

  ntimes _ ValVoid          = ValVoid
  ntimes n (ValZ z)         = ValZ (ntimes n z)
  ntimes n (ValChain chs)   = ValChain (ntimes n chs)
  ntimes n (ValHmgClass hs) = ValHmgClass (ntimes n hs)

instance (Simplical s x, Typeable v) => Abelian (AbelianValue v s x) where
  negate ValVoid          = ValVoid
  negate (ValZ z)         = ValZ (negate z)
  negate (ValChain chs)   = ValChain (negate chs)
  negate (ValHmgClass hs) = ValHmgClass (negate hs)

  ValVoid - ValVoid             = ValVoid
  ValZ a - ValZ b               = ValZ (a-b)
  ValChain a - ValChain b       = ValChain (a-b)
  ValHmgClass h - ValHmgClass h'= ValHmgClass (h-h')

  ztimes _ ValVoid          = ValVoid
  ztimes n (ValZ z)         = ValZ (ztimes n z)
  ztimes n (ValChain chs)   = ValChain (ztimes n chs)
  ztimes n (ValHmgClass hs) = ValHmgClass (ztimes n hs)

--------------------------------------------------------------------------------
-- AblVars -

newtype AblVars v s x = AblVars (M.Map (Z,String) (AbelianExpression v s x))

--------------------------------------------------------------------------------
-- evalAblVar -

evalAblVar :: AblVars v s x -> Z -> String -> Eval (AbelianExpression v s x)
evalAblVar (AblVars bnds) at name = case (at,name) `M.lookup` bnds of
  Just axpr -> return axpr
  Nothing   -> failure $ NoSuchVariable at name

--------------------------------------------------------------------------------
-- Vars -

data Vars s x
  = Vars (AblVars () s x) (AblVars Z s x)
         (AblVars (Vec (ChainValueAt s x)) s x)
         (AblVars (Vec AbElement) s x)

--------------------------------------------------------------------------------
-- ablVars -

ablVars :: Vars s x -> AbelianExpressionType v s x -> AblVars v s x
ablVars (Vars vV vZ vC vH) t = case t of
  AblExprTypeVoid     -> vV
  AblExprTypeZ        -> vZ
  AblExprTypeChain    -> vC
  AblExprTypeHmgClass -> vH

--------------------------------------------------------------------------------
-- evalVar -

evalVar :: Vars s x -> AbelianExpressionType v s x -> Z -> String -> Eval (AbelianExpression v s x)
evalVar vrs t = evalAblVar (ablVars vrs t)

--------------------------------------------------------------------------------
-- evalAblValType -

-- | evaluation to the type of a abelian expression. 
evalAblValType ::
  ( Simplical s x
  , Typeable v
  )
  => Vars s x -> AbelianExpressionType v s x
  -> Z -> AbelianExpression v s x -> Eval (AbelianValueType v s x)
evalAblValType vrs te at e    = case e of
  AblExprValue v             -> return $ root v
  AblExprVariable name       -> evalVar vrs te at name >>= evalAblValType vrs te at
  AblExprZero t              -> return t
  _ :!> e'                   -> evalAblValType vrs te at e'
  a :+: b                    -> do
    ta <- evalAblValType vrs te at a
    tb <- evalAblValType vrs te at b
    case ta == tb of
      True                   -> return ta
      False                  -> failure NotAddableExpressions      
  f :$: a                    -> case f of
    AblOprChainAll _         -> return $ AblValTypeChain at
    AblOprChainAt _          -> return $ AblValTypeChain at    
    AblOprBoundary           -> do
      ta <- evalAblValType vrs te at a
      case ta of
        AblValTypeChain at' -> return $ AblValTypeChain (pred at')

--------------------------------------------------------------------------------
-- evalBoundarySumForm -

evalBoundarySumForm :: Env t s n x
  ->       SumForm Z (AbelianValue (Vec (ChainValueAt s x)) s x)
  -> Eval (SumForm Z (AbelianValue (Vec (ChainValueAt s x)) s x))
evalBoundarySumForm env sf = case sf of
  Zero r               -> case r of
    AblValTypeChain at -> return $ Zero $ AblValTypeChain (pred at)
  S (ValChain chs)     -> evalBoundaryVec env chs >>= return . S . ValChain
  z :! a               -> evalBoundarySumForm env a >>= return . (z:!)
  a :+ b               -> do
    a' <- evalBoundarySumForm env a
    b' <- evalBoundarySumForm env b
    return (a' :+ b')

--------------------------------------------------------------------------------
-- evalAblValSumForm -

-- | evluation to a 'SumForm'.
evalAblValSumForm :: Env t s n x -> Vars s x -> AbelianExpressionType v s x
  -> Z -> AbelianExpression v s x -> Eval (SumForm Z (AbelianValue v s x))
evalAblValSumForm env@Env{} vrs te at e = case e of
  AblExprValue a       -> return $ S a
  AblExprVariable name -> evalVar vrs te at name >>= evalAblValSumForm env vrs te at
  AblExprZero t        -> return $ Zero t  
  z :!> a              -> do
    vz <- evalAblValZ env vrs AblExprTypeZ at z
    sa <- evalAblValSumForm env vrs te at a
    return (vz :! sa)
  a :+: b              -> do
    sa <- evalAblValSumForm env vrs te at a
    sb <- evalAblValSumForm env vrs te at b
    return (sa :+ sb)    
  f :$: a             -> case f of

    AblOprChainAll t  -> error "nyi"
    
    AblOprChainAt t   -> do
      za <- evalAblValZ env vrs AblExprTypeZ at a
      ch <- evalChainVecAt env t at za
      return $ S $ ValChain ch

    AblOprBoundary    -> evalAblValSumForm env vrs te at a >>= evalBoundarySumForm env

--------------------------------------------------------------------------------
-- evalAblVal -

type HomFib h = Path h
type HomFibEmpty s = HomFib (HomEmpty s)

evalAblVal :: Typeable v
  => Env t s n x -> Vars s x -> AbelianExpressionType v s x
  -> Z -> AbelianExpression v s x -> Eval (AbelianValue v s x)
evalAblVal env@Env{} vrs te at e = do
  s <- evalAblValSumForm env vrs te at e
  return $ zSum vOne $ make s

  where vOne :: (Typeable v, Simplical s x)
             => HomFibEmpty Fbr (AbelianValue v s x) (AbelianValue v s x)
        vOne = cOne Struct

--------------------------------------------------------------------------------
-- evalAblValZ -

evalAblValZ :: Env t s n x -> Vars s x -> AbelianExpressionType Z s x
  -> Z -> AbelianExpression Z s x -> Eval Z
evalAblValZ env vrs te at e = evalAblVal env vrs te at e >>= return . (\(ValZ z) -> z) 
{-
--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression s x where
  ExprMaxDim     :: Expression s x
  ExprCardSmpSet :: CardinalitySimplexSetExpression s x -> Expression s x
  ExprHmgGroup   :: HomologyGroupExpression s x -> Expression s x
  ExprChns       :: ChainType -> Expression s x
  ExprAbl        :: Typeable v => AbelianExpressionType v s x -> AbelianExpression v s x
                 -> Expression s x

--------------------------------------------------------------------------------
-- CardinalitySimplexSetExpression -

data CardinalitySimplexSetExpression (s :: Type -> Type) x
  = ExprCardSmpSetAll
  | ExprCardSmpSetAt

--------------------------------------------------------------------------------
-- HomologyGroupExpression -

data HomologyGroupExpression (s :: Type -> Type) x
  = ExprHmgGroupAll
  | ExprHmgGroupAt
  
--------------------------------------------------------------------------------
-- Value -

data Value s x where
  ValMaxDim     :: Z -> Value s x
  ValCardSmpSet :: Attestable n => Cards Z n -> Value s x
  ValHmgGroup   :: Attestable n => Deviation (n+1) AbHom -> Value s x
  ValChns       :: ChainList s x -> Value s x
  ValAbl        :: Typeable v => AbelianValue v s x -> Value s x

deriving instance Simplical s x => Show (Value s x)

--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> Vars s x -> Z -> Expression s x -> Eval (Value s x)
eval env@Env{} vrs at expr        = case expr of
  ExprMaxDim               -> return $ ValMaxDim $ envMaxDim env
  ExprCardSmpSet cexpr     -> case cexpr of
    ExprCardSmpSetAll      -> return $ ValCardSmpSet $ evalCardSmpSetAll env
    ExprCardSmpSetAt       -> evalCardSmpSetAt env at >>= return . ValCardSmpSet
  ExprHmgGroup hexpr       -> case hexpr of
    ExprHmgGroupAll        -> return $ ValHmgGroup $ evalHmgGroupAll env
    ExprHmgGroupAt         -> evalHmgGroupAt env at >>= return . ValHmgGroup
  ExprChns ct              -> evalChainsAt env ct at >>= return . ValChns                
  ExprAbl ta aexpr         -> evalAblVal env vrs ta at aexpr >>= return . ValAbl

    
vrs = Vars (AblVars M.empty) (AblVars M.empty) (AblVars M.empty)


maxDim = ExprMaxDim

hmgs  = ExprHmgGroup ExprHmgGroupAll
hmg   = ExprHmgGroup ExprHmgGroupAt

crds  = ExprCardSmpSet ExprCardSmpSetAll
crd   = ExprCardSmpSet ExprCardSmpSetAt

chsAt = ExprChns


-- chAt t i = ExprAbl AblExprTypeChain (AblOprChainAt t :$: AblExprValue (ValZ i))
ablExprCh :: Simplical s x => AbelianExpression (ChainValue s x) s x -> Expression s x
ablExprCh = ExprAbl AblExprTypeChain

vlz = AblExprValue . ValZ

chAt t i = AblOprChainAt t :$: AblExprValue (ValZ i)

dAt ch = ExprAbl AblExprTypeChain (AblOprBoundary :$: ch)
-}

{-
chAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Chain

cysAt = ChainExpr (ChainListAtExpr Cycle)
cyAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Cycle

hgwAt = ChainExpr (ChainListAtExpr Homology)
hgAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Homology

hcAt t i = ChainExpr (ChainApplicationAtExpr HomologyClass (ChainSumFormAt $ S $ R $ ChainIndex t i))

dAt t i = ChainExpr (ChainApplicationAtExpr Boundary (ChainSumFormAt $ S $ R $ ChainIndex t i))
-}
