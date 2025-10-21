
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

import Data.Kind
import Data.Foldable (toList)
import Data.Array as A
import Data.List as L (zip,foldl)
import qualified Data.Map as M

import OAlg.Prelude as P

import OAlg.Data.Proxy
import OAlg.Data.Constructable
import OAlg.Data.Canonical

import OAlg.Structure.Exception
import OAlg.Structure.Oriented hiding (Path(..))
import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Vectorial as V hiding (Vec)

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
  then return (xs A.! i)
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
-- ChainAt -

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


instance Simplical s x => Vectorial (ChainAt s x) where
  type Scalar (ChainAt s x) = Z
  z ! (ChainAt d ch) = ChainAt d (z V.! ch)

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

--------------------------------------------------------------------------------
-- evalVecBoundaryInv -

evalVecBoundaryInv :: Env t s n x -> Vec (ChainAt s x) -> Eval (Vec (ChainAt s x))
evalVecBoundaryInv = error "nyi"

--------------------------------------------------------------------------------
-- evalChainAtHomologyClass -

evalChainAtHomologyClass :: Env t s n x -> ChainAt s x -> Eval AbElement
evalChainAtHomologyClass env (ChainAt at ch) = do
  e     <- evalToAbElement env at ch
  (_,h) <- evalAt env at
  homologyClass h e
  
--------------------------------------------------------------------------------
-- evalVecHomologyClass -

evalVecHomologyClass :: Env t s n x -> Vec (ChainAt s x) -> Eval (Vec AbElement)
evalVecHomologyClass env v = do
  hs <- evalHmgGroupAt env at
  case hs of
    DiagramDiscrete (h:|_) -> do
      vh <- psqSequence $ psqMap (evalChainAtHomologyClass env) chs
      return $ make $ VectorGForm h vh
    
  where VectorGForm at chs = form v

--------------------------------------------------------------------------------
-- evalLookup -

evalLookup :: M.Map (Z,String) x -> Z -> String  -> Eval x
evalLookup m at n = case M.lookup (at,n) m of
  Just x  -> return x
  Nothing -> failure $ UnboundVariable at n

--------------------------------------------------------------------------------
-- AbelianExpression -

data AbelianExpression t h v where
  AblExprValue    :: v -> AbelianExpression t h v
  AblExprVariable :: t v -> String -> AbelianExpression t h v 
  AblExprZero     :: Root v -> AbelianExpression t h v
  (:!>)           :: AbelianExpression t h Z -> AbelianExpression t h v -> AbelianExpression t h v
  (:+:)           :: AbelianExpression t h v -> AbelianExpression t h v -> AbelianExpression t h v
  (:$:)           :: h u v -> AbelianExpression t h u -> AbelianExpression t h v

--------------------------------------------------------------------------------
-- HomologyValueType -

data HomologyValueType s x v where
  HmgValTypeVoid  :: HomologyValueType s x ()
  HmgValTypeZ     :: HomologyValueType s x Z
  HmgValTypeChain :: HomologyValueType s x (Vec (ChainAt s x)) 

--------------------------------------------------------------------------------
-- evalRootHmgValType -

evalRootHmgValType :: Z -> HomologyValueType s x v -> Eval (Root v)
evalRootHmgValType at t = case t of
  HmgValTypeVoid  -> return (():>())
  HmgValTypeZ     -> return (():>())
  HmgValTypeChain -> return at

--------------------------------------------------------------------------------
-- HomologyOperator -

data HomologyOperator s x u v where
  HmgOprChainAll    :: ChainType -> HomologyOperator s x () (Vec (ChainAt s x))
  HmgOprChainAt     :: ChainType -> HomologyOperator s x Z (Vec (ChainAt s x))
  HmgOprBoundary    :: HomologyOperator s x (Vec (ChainAt s x)) (Vec (ChainAt s x))
  HmgOprBoundaryInv :: HomologyOperator s x (Vec (ChainAt s x)) (Vec (ChainAt s x)) 
  HmgOprClass       :: HomologyOperator s x (Vec (ChainAt s x)) (Vec AbElement)

instance Simplical s x => Morphism (HomologyOperator s x) where
  type ObjectClass (HomologyOperator s x) = (Abl,Ord')
  homomorphous (HmgOprChainAll _) = Struct :>: Struct
  homomorphous (HmgOprChainAt _)  = Struct :>: Struct
  homomorphous HmgOprBoundary     = Struct :>: Struct
  homomorphous HmgOprBoundaryInv  = Struct :>: Struct
  homomorphous HmgOprClass        = Struct :>: Struct
  
--------------------------------------------------------------------------------
-- evalHmgOpr -

evalHmgOpr :: Env t s n x -> Z -> HomologyOperator s x u v -> u -> Eval v
evalHmgOpr env at (HmgOprChainAll t) () = evalVecChainsAt env t at
evalHmgOpr env at (HmgOprChainAt t) z   = evalVecChainAt env t at z
evalHmgOpr env _  HmgOprBoundary chs    = evalVecBoundary env chs
evalHmgOpr env _  HmgOprBoundaryInv chs = evalVecBoundaryInv env chs 
evalHmgOpr env _  HmgOprClass chs       = evalVecHomologyClass env chs

--------------------------------------------------------------------------------
-- evalRootHmgOpr -

evalRootHmgOpr :: Env t s n x -> Z -> HomologyOperator s x u v -> Root u -> Eval (Root v)
evalRootHmgOpr env at (HmgOprChainAll _) (():>())
  | -2 < at && at < envMaxDim env + 2   = return at
  | otherwise                           = failure $ AtOutOfRange at
evalRootHmgOpr env at (HmgOprChainAt _) (():>())
  | -2 < at && at < envMaxDim env + 2   = return at
  | otherwise                           = failure $ AtOutOfRange at
evalRootHmgOpr env _ HmgOprBoundary at'
  | -1 < at' && at' < envMaxDim env + 2 = return (pred at')
  | otherwise                           = failure $ AtOutOfRange at'
evalRootHmgOpr env _ HmgOprBoundaryInv at'
  | -1 < at' && at' < envMaxDim env + 1 = return (succ at')
  | otherwise                           = failure $ AtOutOfRange at'
evalRootHmgOpr env _ HmgOprClass at'
  | -1 < at' && at' < envMaxDim env + 1 = do
      h <- evalHmgGroupAt env at'
      case h of DiagramDiscrete gs     -> return $ head gs
  | otherwise                           = failure $ AtOutOfRange at'

--------------------------------------------------------------------------------
-- HomologyExpr -

type HomologyExpr s x = AbelianExpression (HomologyValueType s x) (HomologyOperator s x)

--------------------------------------------------------------------------------
-- evalRootHmgExpr -

-- | the root of a 'HomologyExpr' which serves to check wether the expression is well formed.
evalRootHmgExpr :: Fibred v => Env t s n x -> Z -> HomologyExpr s x v -> Eval (Root v)
evalRootHmgExpr env@Env{} at e = case e of
  AblExprValue v      -> return $ root v
  AblExprVariable t _ -> evalRootHmgValType at t
  AblExprZero r       -> return r
  _ :!> a             -> evalRootHmgExpr env at a
  a :+: b             -> do
    ra <- evalRootHmgExpr env at a
    rb <- evalRootHmgExpr env at b
    case ra == rb of
      True            -> return ra
      False           -> failure NotAddableExpression
  f :$: a             -> case P.domain f of
    Struct            -> evalRootHmgExpr env at a >>= evalRootHmgOpr env at f


--------------------------------------------------------------------------------
-- Vars -

data Vars s x
  = Vars { vrsVoid  :: M.Map (Z,String) (HomologyExpr s x ())
         , vrsZ     :: M.Map (Z,String) (HomologyExpr s x Z)
         , vrsChain :: M.Map (Z,String) (HomologyExpr s x (Vec (ChainAt s x)))
         }

--------------------------------------------------------------------------------
-- evalVar -

evalVar :: Vars s x
  -> HomologyValueType s x v -> Z -> String -> Eval (HomologyExpr s x v)
evalVar vrs t z n = case t of
  HmgValTypeVoid  -> evalLookup (vrsVoid vrs) z n
  HmgValTypeZ     -> evalLookup (vrsZ vrs) z n
  HmgValTypeChain -> evalLookup (vrsChain vrs) z n

--------------------------------------------------------------------------------
-- evalSumFormHmgOpr -

evalSumFormHmgOpr :: Env t s n x -> Z -> HomologyOperator s x u v -> SumForm Z u -> Eval (SumForm Z v)
evalSumFormHmgOpr env at h s = case s of
  Zero r -> evalRootHmgOpr env at h r >>= return . Zero
  S u    -> evalHmgOpr env at h u >>= return . S
  z :! a -> evalSumFormHmgOpr env at h a >>= return . (z:!)
  a :+ b -> do
    a' <- evalSumFormHmgOpr env at h a
    b' <- evalSumFormHmgOpr env at h b
    return (a' :+ b')
    
--------------------------------------------------------------------------------
-- evalSumFormHmgExpr -

evalSumFormHmgExpr :: (Abelian v, Ord v)
  => Env t s n x -> Vars s x
  ->  Z -> HomologyExpr s x v -> Eval (SumForm Z v)
evalSumFormHmgExpr env@Env{} vrs at e = case e of
  AblExprValue v      -> return $ S v
  AblExprVariable t n -> evalVar vrs t at n >>= evalSumFormHmgExpr env vrs at
  AblExprZero r       -> return $ Zero r
  z :!> a             -> do
    z' <- evalHmgExpr env vrs at z
    a' <- evalSumFormHmgExpr env vrs at a
    return (z' :! a')
  a :+: b             -> do
    a' <- evalSumFormHmgExpr env vrs at a
    b' <- evalSumFormHmgExpr env vrs at b
    return (a' :+ b')
  h :$: u             -> case P.domain h of
    Struct -> evalSumFormHmgExpr env vrs at u >>= evalSumFormHmgOpr env at h

--------------------------------------------------------------------------------
-- evalHmgExpr -

evalHmgExpr :: (Abelian v, Ord v)
  => Env t s n x -> Vars s x -> Z -> HomologyExpr s x v -> Eval v
evalHmgExpr env@Env{} vrs at e =  do
  s <- evalSumFormHmgExpr env vrs at e
  return $ zSum vOne $ make s

  where vOne :: Abelian v
             => HomFibEmpty Fbr v v
        vOne = cOne Struct

--------------------------------------------------------------------------------
-- Expr -

-- | expression to evaluate values of type t'Value'.
data Expr n s x v where
  ExprMaxDim     :: Expr n s x Z  
  ExprCardSmpSet :: CardinalitySimplexSetExpr n s x v -> Expr n s x v
  ExprHmgGroup   :: HomologyGroupExpr n s x v -> Expr n s x v
  ExprHmg        :: (Abelian v, Ord v) => HomologyExpr s x v -> Expr n s x v

--------------------------------------------------------------------------------
-- CardinalitySimplexSetExpr -

data CardinalitySimplexSetExpr n (s :: Type -> Type) x v where
  ExprCardSmpSetAll :: CardinalitySimplexSetExpr n s x (Cards Z n)
  ExprCardSmpSetAt :: CardinalitySimplexSetExpr n s x (Cards Z N0)
  

--------------------------------------------------------------------------------
-- HomologyGroupExpr -

data HomologyGroupExpr n (s :: Type -> Type) x v where
  ExprHmgGroupAll :: HomologyGroupExpr n s x (Deviation (n+1) AbHom)
  ExprHmgGroupAt  :: HomologyGroupExpr n s x (Deviation N1 AbHom)

--------------------------------------------------------------------------------
-- eval -

eval :: Env t s n x -> Vars s x -> Z -> Expr n s x v -> Eval v
eval env@Env{} vrs at e = case e of
  ExprMaxDim           -> return $ envMaxDim env      
  ExprCardSmpSet c     -> case c of
    ExprCardSmpSetAll  -> return $ evalCardSmpSetAll env    
    ExprCardSmpSetAt   -> evalCardSmpSetAt env at
  ExprHmgGroup h       -> case h of
    ExprHmgGroupAll    -> return $ evalHmgGroupAll env
    ExprHmgGroupAt     -> evalHmgGroupAt env at    
  ExprHmg h            -> evalHmgExpr env vrs at h



t = ChainComplexStandard
n = attest :: Any N6
a = complex [Set "ab",Set "bc",Set "cd"]
b = complex [Set[0,1],Set[1,2],Set[0,2],Set[1,2,3]] :: Complex N
s = Proxy :: Proxy Asc

ea = env' s t n a
eb = env' s t n b

vrs = Vars (M.empty) (M.empty) (M.empty)

maxDim = ExprMaxDim

hmgs  = ExprHmgGroup ExprHmgGroupAll
hmg   = ExprHmgGroup ExprHmgGroupAt

crds  = ExprCardSmpSet ExprCardSmpSetAll
crd   = ExprCardSmpSet ExprCardSmpSetAt

-- chsAt = ExprChns


ablExprCh :: (Abelian v, Ord v) => HomologyExpr s x v -> Expr n s x v
ablExprCh = ExprHmg

vl :: (Abelian v, Ord v) => v -> Expr n s x v
vl = ExprHmg . AblExprValue


chs t  = HmgOprChainAll t :$: AblExprValue ()
chAt t i = HmgOprChainAt t :$: AblExprValue i

dAt = (:$:) HmgOprBoundary 

hAt = (:$:) HmgOprClass

(.+.) = (:+:)
