
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
import Data.List as L (zip,(++),foldl)
import qualified Data.Map as M

import OAlg.Prelude

import OAlg.Data.Proxy
-- import OAlg.Data.Either
-- import OAlg.Data.Reducible
-- import OAlg.Data.Constructable
import OAlg.Data.Canonical

import OAlg.Structure.Oriented
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
-- import OAlg.Structure.Distributive
-- import OAlg.Structure.Exponential

import OAlg.Entity.Diagram hiding (Chain)
import OAlg.Entity.Natural hiding (S)
import OAlg.Entity.FinList as F hiding ((++))
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum
-- import OAlg.Entity.Slice.Free
import OAlg.Entity.Matrix

-- import OAlg.Hom.Distributive

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
{-
--------------------------------------------------------------------------------
-- ChainIndex -

data ChainIndex = ChainIndex ChainType N deriving (Show,Eq,Ord)

instance Validable ChainIndex where
  valid (ChainIndex t n) = valid n && case t of
    Chain -> SValid
    _     -> SValid

--------------------------------------------------------------------------------
-- VarBind -

newtype VarBind s x = VarBind (M.Map (N,String) (ChainValue s x))
-}

--------------------------------------------------------------------------------
-- SomeChainComplex -

-- | ignoring the 'ChainComplexType'.
data SomeChainComplex r s n x where
  SomeChainComplex ::  ChainComplex t r s n x -> SomeChainComplex r s n x

--------------------------------------------------------------------------------
-- Env -

data Env t s n x where
  Env :: (Simplical s x, Attestable n)
    => { envMaxDim       :: Z
       , envChainComplex :: ChainComplex t Z s n x
       , envHomology     :: Homology n
       , envAt           :: Array Z (SomeChainComplex Z s N0 x, Homology N0)
       , envSimplexSets  :: Array Z (Set (s x))     -- ^ base for the chains.
       , envCycles       :: Array Z (ChainList s x) -- ^ base of cyles.
       , envHomologies   :: Array Z (ChainList s x) -- ^ generators for the homology classes.
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
             , envCycles       = cys
             , envHomologies   = hms
             } where
    
    dm   = inj (lengthN n)
    ccx  = chainComplex t n c
    hmg  = homology ccx
    ats  = ccxhmg n ccx hmg
    
    smps = array (-1,dm+1) ([-1..] `L.zip` (toList $ dgPoints $ ccxDiagram ccx))
    at   = array (0,dm) ([0..] `L.zip` toList ats)
    cys  = array (0,dm) ([0..] `L.zip` (toList $ amap1 cycles ats))
    hms  = array (0,dm) ([0..] `L.zip` (toList $ amap1 homologies ats))
    
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

evalElmAt :: Ix i => EvalFailure -> Array i x -> i -> Eval x
evalElmAt f xs i = if (bounds xs `inRange` i) then return (xs ! i) else failure f

--------------------------------------------------------------------------------
-- evalAt -

evalAt :: Env t s n x -> Z -> Eval (SomeChainComplex Z s N0 x,Homology N0)
evalAt env at = evalElmAt (IndexOutOfRange at) (envAt env) at 


--------------------------------------------------------------------------------
-- evalSimplexSet -

-- | evaluates the simplex set according to the given environment @enf@ and the given index
-- in the range @-1,0..n'+'1@ where @n = 'envMaxDim' env@. If the givne index is not in the
-- defined range then the evaluation yields a 'IndexOutOfRange' 'failure'.
evalSimplexSet :: Env t s n x -> Z -> Eval (Set (s x))
evalSimplexSet env@Env{} at = evalElmAt (IndexOutOfRange at) (envSimplexSets env) at 

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
-- evalCardSmplSetAll -

evalCardSmplSetAll :: Env t s n x -> Cards Z n
evalCardSmplSetAll env@Env{} = ccxCards $ envChainComplex env

--------------------------------------------------------------------------------
-- evalCardSmplSetAt ´-

evalCardSmplSetAt :: Env t s n x -> Z -> Eval (Cards Z N0)
evalCardSmplSetAt env@Env{} i = do
  SomeChainComplex ccx <- evalAt env i >>= return . fst
  return $ ccxCards ccx

--------------------------------------------------------------------------------
-- evalHomologyGroups -

evalHomologyGroups :: Env t s n x -> Deviation (n+1) AbHom
evalHomologyGroups env@Env{} = homologyGroups $ envHomology env

--------------------------------------------------------------------------------
-- evalHomologyGroupAt -

evalHomologyGroupAt :: Env t s n x -> Z -> Eval (Deviation N1 AbHom)
evalHomologyGroupAt env i = evalAt env i >>= return . homologyGroups . snd

--------------------------------------------------------------------------------
-- AbelianExpressionType -

data AbelianExpressionType t s x where
  AblExprTypeZ        :: AbelianExpressionType Z s x
  AblExprTypeChain    :: Z -> AbelianExpressionType (ChainValue s x) s x
  AblExprTypeHmgClass :: AbGroup -> AbelianExpressionType AbGroup s x
  
deriving instance Show (AbelianExpressionType t s x)
deriving instance Eq (AbelianExpressionType t s x)
instance Validable (AbelianExpressionType t s x) where
  valid t = Label "AbelianExpressionType" :<=>: case t of
    AblExprTypeHmgClass g -> valid g
    AblExprTypeChain z    -> valid z
    AblExprTypeZ          -> SValid

--------------------------------------------------------------------------------
-- AbelianOperator -

data AbelianOperator t (s :: Type -> Type) x where
  AblOprChainAt :: ChainType -> AbelianExpression Z s x -> AbelianOperator (ChainValue s x) s x

deriving instance Simplical s x => Show (AbelianOperator t s x)

--------------------------------------------------------------------------------
-- AbelianExpression -

data AbelianExpression t s x where
  AblExprValue    :: AbelianValue t s x -> AbelianExpression t s x
  AblExprVariable :: AbelianVariable t s x -> AbelianExpression t s x
  AblExprZero     :: AbelianExpressionType t s x -> AbelianExpression t s x
  (:!>)           :: AbelianExpression Z s x -> AbelianExpression t s x -> AbelianExpression t s x
  (:+:)           :: AbelianExpression t s x -> AbelianExpression t s x -> AbelianExpression t s x
  (:$:)           :: AbelianOperator t s x -> AbelianExpression t s x -> AbelianExpression t s x
  

deriving instance Simplical s x => Show (AbelianExpression t s x)

--------------------------------------------------------------------------------
-- AbelianValue -

data AbelianValue t s x where
  ValZ        :: Z -> AbelianValue Z s x
  ValChain    :: Z -> ChainValue s x -> AbelianValue (ChainValue s x) s x
  ValHmgClass :: AbElement -> AbelianValue AbGroup s x 

deriving instance Simplical s x => Show (AbelianValue t s x)
deriving instance Simplical s x => Eq (AbelianValue t s x)

instance Simplical s x => Validable (AbelianValue t s x) where
  valid v = Label "AbelianValue" :<=>: case v of
    ValZ z        -> valid z
    ValChain z ch -> And [ valid z
                         , valid ch
                         , vldValChain z (ssylc ch)
                         ]
    ValHmgClass e -> valid e

    where
      vldValChain :: Simplical s x => Z -> LinearCombination Z (s x) -> Statement
      vldValChain z (LinearCombination chs)
        = foldl (vldHomogenDim z) SValid $ amap1 snd chs


      vldHomogenDim :: Simplical s x => Z -> Statement -> s x -> Statement
      vldHomogenDim z v sx = v && (z == dimension sx) :?> Params ["z":=show z, "sx":=show sx]

type instance Root (AbelianValue t s x) = AbelianExpressionType t s x

deriving instance ShowRoot (AbelianValue t s x)
deriving instance EqRoot (AbelianValue t s x)
deriving instance ValidableRoot (AbelianValue t s x)
deriving instance (Typeable s, Typeable t, Typeable x) => TypeableRoot (AbelianValue t s x)

instance (Simplical s x, Typeable t) => Fibred (AbelianValue t s x) where
  root (ValZ _)        = AblExprTypeZ
  root (ValChain z _)  = AblExprTypeChain z
  root (ValHmgClass e) = AblExprTypeHmgClass (end e) 

instance (Simplical s x, Typeable t) => Additive (AbelianValue t s x) where
  zero AblExprTypeZ            = ValZ (zero (():>()))
  zero (AblExprTypeChain z)    = ValChain z (zero ())
  zero (AblExprTypeHmgClass g) = ValHmgClass (zero g)
  
--------------------------------------------------------------------------------
-- AbelianVariable -

newtype AbelianVariable t (s :: Type -> Type) x = AblVar String deriving (Show,Eq)

--------------------------------------------------------------------------------
-- Vars -

newtype Vars t (s :: Type -> Type) x = Vars (M.Map (Z,String) (AbelianExpression t s x))

--------------------------------------------------------------------------------
-- evalVar -

evalVar :: Vars t s x -> Z -> String -> Eval (AbelianExpression t s x)
evalVar (Vars bnds) at name = case (at,name) `M.lookup` bnds of
  Just axpr -> return axpr
  Nothing   -> failure $ NoSuchVariable at name
  
--------------------------------------------------------------------------------
-- evalAblExprType -

evalAblExprType ::
  ( Simplical s x
  , Typeable v
  )
  => Vars v s x -> Z -> AbelianExpression v s x -> Eval (AbelianExpressionType v s x)
evalAblExprType vrs at aexpr = case aexpr of
  AblExprValue v           -> return $ root v
  AblExprVariable v        -> case v of
    AblVar name            -> evalVar vrs at name >>= evalAblExprType vrs at
  AblExprZero t            -> return t
  _ :!> aexpr'             -> evalAblExprType vrs at aexpr'
  a :+: b                  -> do
    ta <- evalAblExprType vrs at a
    tb <- evalAblExprType vrs at b
    case ta == tb of
      True                 -> return ta
      False                -> failure NotAddableExpressions
  f :$: a                  -> case f of
    AblOprChainAt _ _      -> return $ AblExprTypeChain at


--------------------------------------------------------------------------------
-- evalSumFormAbelianValueSmf -

evalSumFormAbelianValue :: Env t s n x -> Vars v s x
  -> Z -> AbelianExpression v s x -> Eval (SumForm Z (AbelianValue v s x))
evalSumFormAbelianValue env@Env{} vrs at aexpr = case aexpr of
  AblExprValue v -> return (S v)

{-
--------------------------------------------------------------------------------
-- evalChainValue -

evalChainValueAtEnv :: Env t s n x -> N -> ChainType -> N -> Eval (ChainValue s x)
evalChainValueAtEnv env@Env{} i t j = do
  chsAt <- evalElmAt (envChains env) i (AtOutOfRange i)
  chsTp <- evalElmAt chsAt t (EvalFailure ("unsupported chain type: " L.++ show t))
  evalElmAt chsTp j (IndexOutOfRange $ inj j)

--------------------------------------------------------------------------------
-- evalChainValue -

evalChainValueAtSmf :: Env t s n x -> VarBind s x
  -> N -> SumForm Z (R ChainIndex) -> Eval (ChainValue s x)
evalChainValueAtSmf env@Env{} vrs at sf
  | envMaxDim env < at = failure $ AtOutOfRange at
  | otherwise          = evl env vrs at (reduce sf) >>= return . SumSymbol . make where
  
  evl env vrs at sf = case sf of
    Zero ()  -> return $ Zero ()
    z :! sf' -> evl env vrs at sf' >>= return . (z:!)
    a :+ b   -> do
      a' <- evl env vrs at a
      b' <- evl env vrs at b
      return (a' :+ b')
    S (R (ChainIndex t i)) -> do
      SumSymbol sx <- evalChainValueAtEnv env at t i
      return $ form sx


--------------------------------------------------------------------------------
-- Expression -

-- | expression to evaluate values of type t'Value'.
data Expression
  = MaxDimExpr -- ^ the maximal dimension
  | CardinalityExpr  CardinalityExpression -- ^ cardinality.
  | HomologyGroupExpr HomologyGroupExpression
  | ChainExpr ChainExpression

--------------------------------------------------------------------------------
-- CardinalityExpression -

-- | expression to evaluate values of type t'Cardinality'.
data CardinalityExpression
  = CardSimplexSetAllExpr
  | CardSimplexSetAtExpr

--------------------------------------------------------------------------------
-- HomologyGroupExpression -

-- | expression to evaluate values of type t'HomologyGroup'.
data HomologyGroupExpression
  = HomologyGroupAllExpr
  | HomologyGroupAtExpr

--------------------------------------------------------------------------------
-- ChainListAtExpression -

data ChainExpression
  = ChainListAtExpr ChainType
  | ChainValueAtExpr ChainValueAtExpression
  | ChainApplicationAtExpr ChainOperatorType ChainValueAtExpression

--------------------------------------------------------------------------------
-- ChainExpression -

data ChainValueAtExpression = ChainSumFormAt (SumForm Z (R ChainIndex))

--------------------------------------------------------------------------------
-- ChainOperatorType -

data ChainOperatorType
  = HomologyClass
  | Boundary
  deriving (Show,Eq)  

--------------------------------------------------------------------------------
-- Value -

data Value (s :: Type -> Type) x
  = MaximalDimension N
  | Cardinality (Cardinality s x)
  | HomologyGroup (HomologyGroup s x)
  | ChainList (ChainList s x)
  | ChainValue (ChainValue s x)
  | HomologyClassValue AbElement
  deriving (Show)

--------------------------------------------------------------------------------
-- Cardinality -

data Cardinality (s :: Type -> Type) x where
  SimplexSetCardinalities :: Attestable n => Cards Z n -> Cardinality s x

deriving instance Show (Cardinality s x)

--------------------------------------------------------------------------------
-- HomologyGroup -

data HomologyGroup (s :: Type -> Type) x where
  HomologyGroups :: Attestable n => Deviation (n+1) AbHom -> HomologyGroup s x

deriving instance Show (HomologyGroup s x)

--------------------------------------------------------------------------------
-- evalCardinalityExpr -

evalCardinalityExpr :: Env t s n x -> N -> CardinalityExpression -> Eval (Cardinality s x)
evalCardinalityExpr env@Env{} at cexpr = case cexpr of
  CardSimplexSetAllExpr  -> return $ SimplexSetCardinalities $ evalCardSmplSetAll env
  CardSimplexSetAtExpr -> evalCardSmplSetAt env at >>= return . SimplexSetCardinalities 

--------------------------------------------------------------------------------
-- evalHomologyGroupExpr -

evalHomologyGroupExpr :: Env t s n x -> N -> HomologyGroupExpression -> Eval (HomologyGroup s x)
evalHomologyGroupExpr env@Env{} at hexpr = case hexpr of
  HomologyGroupAllExpr  -> return $ HomologyGroups $ evalHomologyGroups env
  HomologyGroupAtExpr   -> evalHomologyGroupAt env at >>= return . HomologyGroups

--------------------------------------------------------------------------------
-- evalChainListAt -

evalChainListAt :: Env t s n x -> N -> ChainType -> Eval (ChainList s x)
evalChainListAt env at t = do
  chsAt <- evalElmAt (envChains env) at (AtOutOfRange at)
  evalElmAt chsAt t (EvalFailure ("unsupported chain type: " L.++ show t))

--------------------------------------------------------------------------------
-- evalChainValueAt -

evalChainValueAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval (ChainValue s x)
evalChainValueAt env vrs at (ChainSumFormAt sf) = evalChainValueAtSmf env vrs at sf

--------------------------------------------------------------------------------
-- evalHomologyClassAt -

evalHomologyClassAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval AbElement
evalHomologyClassAt env vrs at vexpr = do
  c <- evalChainValueAt env vrs at vexpr
  e  <- evalToAbElement env (inj at) c
  h  <- evalAt env at >>= return . snd
  homologyClass h e

--------------------------------------------------------------------------------
-- evalBoundaryAt -

evalBoundaryAt :: Env t s n x -> VarBind s x -> N -> ChainValueAtExpression -> Eval (ChainValue s x)
evalBoundaryAt env vrs at vexpr = do
  c  <- evalChainValueAt env vrs at vexpr
  e  <- evalToAbElement env (inj at) c
  h  <- evalAt env at >>= return . snd
  e' <- boundary h e
  evalFromAbElement env (pred $ inj at) e'

--------------------------------------------------------------------------------
-- evalChainValueAtExpression -

evalChainValueAtExpression :: Env t s n x -> Z -> ChainValue s x -> Eval ChainValueAtExpression
evalChainValueAtExpression = error "nyi"

--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> VarBind s x -> N -> Expression -> Eval (Value s x)
eval env vrs at expr        = case expr of
  MaxDimExpr               -> return $ MaximalDimension $ envMaxDim env
  CardinalityExpr cexpr    -> evalCardinalityExpr env at cexpr >>= return . Cardinality
  HomologyGroupExpr hexpr  -> evalHomologyGroupExpr env at hexpr >>= return . HomologyGroup
  ChainExpr cexpr          -> case cexpr of
    ChainListAtExpr t      -> evalChainListAt env at t >>= return . ChainList
    ChainValueAtExpr vexpr -> evalChainValueAt env vrs at vexpr >>= return . ChainValue
    ChainApplicationAtExpr HomologyClass vexpr
                           -> evalHomologyClassAt env vrs at vexpr >>= return . HomologyClassValue
    ChainApplicationAtExpr Boundary vexpr
                           -> evalBoundaryAt env vrs at vexpr >>= return . ChainValue

vrs = VarBind $ M.empty

hmgs  = HomologyGroupExpr HomologyGroupAllExpr
hmg   = HomologyGroupExpr HomologyGroupAtExpr

crds  = CardinalityExpr CardSimplexSetAllExpr
crd   = CardinalityExpr CardSimplexSetAtExpr

chsAt = ChainExpr (ChainListAtExpr Chain)
chAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Chain

cysAt = ChainExpr (ChainListAtExpr Cycle)
cyAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Cycle

hgwAt = ChainExpr (ChainListAtExpr Homology)
hgAt  = ChainExpr . ChainValueAtExpr . ChainSumFormAt . S . R . ChainIndex Homology

hcAt t i = ChainExpr (ChainApplicationAtExpr HomologyClass (ChainSumFormAt $ S $ R $ ChainIndex t i))

dAt t i = ChainExpr (ChainApplicationAtExpr Boundary (ChainSumFormAt $ S $ R $ ChainIndex t i))
-}
