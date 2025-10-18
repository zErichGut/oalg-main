
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving, DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}

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
import Data.List as L (zip,foldl)
import qualified Data.Map as M

import OAlg.Prelude

-- import OAlg.Data.Proxy
import OAlg.Data.Constructable
import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.Additive

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural hiding (S)
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sequence.PSequence
import OAlg.Entity.Sum
import OAlg.Entity.Matrix
import OAlg.Entity.VectorG

import OAlg.Hom.Fibred

import OAlg.AbelianGroup.Definition

import OAlg.Limes.Exact.Deviation

import OAlg.Homology.Simplical
import OAlg.Homology.Complex
import OAlg.Homology.ChainOperator hiding (Boundary,boundary)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Definition
import OAlg.Homology.Eval.Core

--------------------------------------------------------------------------------
-- ChainType -

-- | types of chains
data ChainType
  = GeneralType  -- ^ general chains with no restriction.
  | CycleType    -- ^ chains with zero boundary.
  | HomologyType -- ^ cycles with non zero homology classes.
  deriving (Show,Eq,Ord,Enum,Bounded,Ix)

--------------------------------------------------------------------------------
-- Chain -

type Chain s x = ChainG Z s x

--------------------------------------------------------------------------------
-- ChainList -

type ChainList s x = Array Z (Chain s x)

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

    base :: Simplical s x => Set (s x) -> Array Z (Chain s x)
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
evalToAbElement :: Env t s n x -> Z -> Chain s x -> Eval AbElement
evalToAbElement env@Env{} at e = do
  ssx <- evalSimplexSet env at
  toAbElm ssx e

  where
    toAbElm :: Simplical s x => Set (s x) -> Chain s x -> Eval AbElement
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
evalFromAbElement :: Env t s n x -> Z -> AbElement -> Eval (Chain s x)
evalFromAbElement env@Env{} at e = do
  ssx <- evalSimplexSet env at
  fromAbElm ssx e
  
  where
    fromAbElm :: Simplical s x => Set (s x) -> AbElement -> Eval (Chain s x)
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

evalChainAt :: Env t s n x -> ChainType -> Z -> Z -> Eval (Chain s x)
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

evalBoundaryAt :: Env t s n x -> Z -> Chain s x -> Eval (Chain s x)
evalBoundaryAt env at ch = do
  e  <- evalToAbElement env at ch
  h  <- evalAt env at >>= return . snd
  e' <- boundary h e
  evalFromAbElement env (pred at) e'

--------------------------------------------------------------------------------
-- Vec -

type Vec = VectorG Z

--------------------------------------------------------------------------------
-- ChainVec -

data ChainAt s x = ChainAt Z (Chain s x) deriving (Show,Eq,Ord)

instance Simplical s x => Validable (ChainAt s x) where
  valid (ChainAt d xs) = Label "ChainAt" :<=>:
    And [ valid xs
        , foldl (vld d) SValid (amap1 snd $ lcs $ ssylc xs)
        ] where

    vld :: Simplical s x => Z -> Statement -> s x -> Statement
    vld d s sx = And [ s
                     , Label "dim" :<=>: (d == dimension sx) :?> Params ["d":=show d, "sx":=show sx]
                     ]

type instance Root (ChainAt s x) = Z
instance ShowRoot (ChainAt s x)
instance EqRoot (ChainAt s x)
instance OrdRoot (ChainAt s x)
instance ValidableRoot (ChainAt s x)
instance TypeableRoot (ChainAt s x)

instance Simplical s x => Fibred (ChainAt s x) where
  root (ChainAt d _) = d

instance Simplical s x => Additive (ChainAt s x) where
  zero d = ChainAt d (zero ())

  ChainAt d a + ChainAt d' b | d == d'   = ChainAt d (a+b)
                             | otherwise = throw NotAddable

  ntimes n (ChainAt d sx) = ChainAt d (ntimes n sx)

instance Simplical s x => Abelian (ChainAt s x) where
  negate (ChainAt d sx) = ChainAt d (negate sx)

  ChainAt d a - ChainAt d' b | d == d'   = ChainAt d (a-b)
                             | otherwise = throw NotAddable
  
  ztimes z (ChainAt d sx) = ChainAt d (ztimes z sx)


--------------------------------------------------------------------------------
-- evalVecChainsAt

evalVecChainsAt :: Env t s n x -> ChainType -> Z -> Eval (Vec (ChainAt s x))
evalVecChainsAt env@Env{} t at = do
  chs <- evalChainsAt env t at
  return $ make
         $ VectorGForm at
         $ PSequence
         $ amap1 (\(i,c) -> (ChainAt at c,i))
         $ assocs chs

--------------------------------------------------------------------------------
-- evalVecChainAt -

evalVecChainAt :: Env t s n x -> ChainType -> Z -> Z -> Eval (Vec (ChainAt s x))
evalVecChainAt env@Env{} t at i = do
  ch <- evalChainAt env t at i
  return $ make
         $ VectorGForm at
         $ PSequence
         $ [(ChainAt at ch,0)]

--------------------------------------------------------------------------------
-- evalChainAtBoundary -

evalChainAtBoundary :: Env t s n x -> ChainAt s x -> Eval (ChainAt s x)
evalChainAtBoundary env (ChainAt at ch)
  = evalBoundaryAt env at ch >>= return . ChainAt (pred at)

--------------------------------------------------------------------------------
-- evalVecBoundary -

evalVecBoundary :: Env t s n x -> Vec (ChainAt s x) -> Eval (Vec (ChainAt s x))
evalVecBoundary env@Env{} v
  = (psqSequence $ psqMap (evalChainAtBoundary env) chs) >>= return . make . VectorGForm (pred at)
  where VectorGForm at chs = form v

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
  AblExprTypeChain    :: AbelianExpressionType (Vec (ChainAt s x)) s x
  AblExprTypeHmgClass :: AbelianExpressionType (Vec AbElement) s x

--------------------------------------------------------------------------------
-- AbelianOperator -

data AbelianOperator v s x where
  AblOprChainAll :: ChainType -> AbelianOperator ((),Vec (ChainAt s x)) s x
  AblOprChainAt  :: ChainType -> AbelianOperator (Z,Vec (ChainAt s x)) s x
  AblOprBoundary :: AbelianOperator (Vec (ChainAt s x),Vec (ChainAt s x)) s x

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
  AblValTypeChain    :: Z -> AbelianValueType (Vec (ChainAt s x)) s x
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
  ValChain    :: Vec (ChainAt s x) -> AbelianValue (Vec (ChainAt s x)) s x
  ValHmgClass :: Vec AbElement -> AbelianValue (Vec AbElement) s x 

deriving instance Simplical s x => Show (AbelianValue v s x)
deriving instance Simplical s x => Eq (AbelianValue v s x)

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
         (AblVars (Vec (ChainAt s x)) s x)
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
-- evalSumFormBoundary -

evalSumFormBoundary :: Env t s n x
  ->       SumForm Z (AbelianValue (Vec (ChainAt s x)) s x)
  -> Eval (SumForm Z (AbelianValue (Vec (ChainAt s x)) s x))
evalSumFormBoundary env sf = case sf of
  Zero r               -> case r of
    AblValTypeChain at -> return $ Zero $ AblValTypeChain (pred at)
  S (ValChain chs)     -> evalVecBoundary env chs >>= return . S . ValChain
  z :! a               -> evalSumFormBoundary env a >>= return . (z:!)
  a :+ b               -> do
    a' <- evalSumFormBoundary env a
    b' <- evalSumFormBoundary env b
    return (a' :+ b')

--------------------------------------------------------------------------------
-- evalSumFormAblVal -

-- | evluation to a 'SumForm'.
evalSumFormAblVal :: Env t s n x -> Vars s x -> AbelianExpressionType v s x
  -> Z -> AbelianExpression v s x -> Eval (SumForm Z (AbelianValue v s x))
evalSumFormAblVal env@Env{} vrs te at e = case e of
  AblExprValue a       -> return $ S a
  AblExprVariable name -> evalVar vrs te at name >>= evalSumFormAblVal env vrs te at
  AblExprZero t        -> return $ Zero t  
  z :!> a              -> do
    vz <- evalAblValZ env vrs AblExprTypeZ at z
    sa <- evalSumFormAblVal env vrs te at a
    return (vz :! sa)
  a :+: b              -> do
    sa <- evalSumFormAblVal env vrs te at a
    sb <- evalSumFormAblVal env vrs te at b
    return (sa :+ sb)    
  f :$: a             -> case f of

    AblOprChainAll t  -> do
      va <- evalAblValVoid env vrs AblExprTypeVoid at a
      case va of () -> evalVecChainsAt env t at >>= return . S . ValChain
    
    AblOprChainAt t   -> do
      za <- evalAblValZ env vrs AblExprTypeZ at a
      ch <- evalVecChainAt env t at za
      return $ S $ ValChain ch

    AblOprBoundary    -> evalSumFormAblVal env vrs te at a >>= evalSumFormBoundary env

--------------------------------------------------------------------------------
-- evalAblVal -

evalAblVal :: Typeable v
  => Env t s n x -> Vars s x -> AbelianExpressionType v s x
  -> Z -> AbelianExpression v s x -> Eval (AbelianValue v s x)
evalAblVal env@Env{} vrs te at e = do
  s <- evalSumFormAblVal env vrs te at e
  return $ zSum vOne $ make s

  where vOne :: (Typeable v, Simplical s x)
             => HomFibEmpty Fbr (AbelianValue v s x) (AbelianValue v s x)
        vOne = cOne Struct

--------------------------------------------------------------------------------
-- evalAblValZ -

evalAblValZ :: Env t s n x -> Vars s x -> AbelianExpressionType Z s x
  -> Z -> AbelianExpression Z s x -> Eval Z
evalAblValZ env vrs te at e = evalAblVal env vrs te at e >>= return . (\(ValZ z) -> z)

--------------------------------------------------------------------------------
-- evalAblValVoid -

evalAblValVoid :: Env t s n x -> Vars s x -> AbelianExpressionType () s x
  -> Z -> AbelianExpression () s x -> Eval ()
evalAblValVoid env vrs te at e = evalAblVal env vrs te at e >>= return . (\ValVoid -> ())

--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression s x where
  ExprMaxDim     :: Expression s x
  ExprCardSmpSet :: CardinalitySimplexSetExpression s x -> Expression s x
  ExprHmgGroup   :: HomologyGroupExpression s x -> Expression s x
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
  ValAbl        :: Typeable v => AbelianValue v s x -> Value s x

deriving instance Simplical s x => Show (Value s x)

instance Simplical s x => Validable (Value s x) where
  valid v = Label "Value" :<=>: case v of
    ValMaxDim z     -> valid z
    ValCardSmpSet c -> valid c
    ValHmgGroup d   -> valid d
    ValAbl a        -> valid a
    
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
  -- ExprChns ct              -> evalChainsAt env ct at >>= return . ValChns                
  ExprAbl ta aexpr         -> evalAblVal env vrs ta at aexpr >>= return . ValAbl


{-

t = ChainComplexStandard
n = attest :: Any N6
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N
s = Proxy :: Proxy Asc

ea = env' s t n a
eb = env' s t n b

vrs = Vars (AblVars M.empty) (AblVars M.empty) (AblVars M.empty) (AblVars M.empty)

maxDim = ExprMaxDim

hmgs  = ExprHmgGroup ExprHmgGroupAll
hmg   = ExprHmgGroup ExprHmgGroupAt

crds  = ExprCardSmpSet ExprCardSmpSetAll
crd   = ExprCardSmpSet ExprCardSmpSetAt

-- chsAt = ExprChns


-- chAt t i = ExprAbl AblExprTypeChain (AblOprChainAt t :$: AblExprValue (ValZ i))
ablExprCh :: Simplical s x => AbelianExpression (Vec (ChainAt s x)) s x -> Expression s x
ablExprCh = ExprAbl AblExprTypeChain

vlz = AblExprValue . ValZ

chsAt t = AblOprChainAll t :$: AblExprValue ValVoid
chAt t i = AblOprChainAt t :$: AblExprValue (ValZ i)

dAt ch = ExprAbl AblExprTypeChain (AblOprBoundary :$: ch)
-}

