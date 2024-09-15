
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE TypeFamilies
           , TypeOperators
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , GADTs
           , StandaloneDeriving
           , DataKinds
#-}


-- |
-- Module      : OAlg.Homology.IO.Interactive
-- Description : intractive mode for handeling homologies.
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- a intractive mode for handeling homologies.
module OAlg.Homology.IO.Interactive
  () where

import Control.Monad
import Control.Applicative
import Control.Exception

import System.IO

import Data.Typeable
import Data.List ((++),reverse,zip,repeat,dropWhile,span,words)
import Data.Foldable (toList,foldl)
import Data.Char (isSpace)
import qualified Data.Map.Strict as M

import OAlg.Prelude hiding (Result(..), It)

import OAlg.Data.Canonical
import OAlg.Data.Constructable
import OAlg.Data.Either

import OAlg.Entity.Natural hiding ((++),S)
import OAlg.Entity.Sequence.Set
import OAlg.Entity.Sum

import OAlg.Structure.Fibred
import OAlg.Structure.Additive
import OAlg.Structure.Multiplicative

import OAlg.AbelianGroup.Definition

import OAlg.Homology.Definition as H
import OAlg.Homology.Complex
import OAlg.Homology.ChainComplex
import OAlg.Homology.Chain
import OAlg.Homology.Simplex

import OAlg.Data.Symbol (Symbol)

--------------------------------------------------------------------------------
-- InteractiveException -

-- | arithmetic exceptions which are sub exceptions of 'SomeOAlgException'.
data InteractiveException
  = UndefinedVariable String
  deriving (Eq,Show)

instance Exception InteractiveException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Term -

infixl 0 :>>
  
data Term
  = Free String -- ^ free variable.
  | Let String Term Term
  | PrimitiveTerm PrimitiveTerm
  | (:>>) Term Term -- ^ application
  | (:+>) Term Term
  | (:!>) Term Term
  deriving (Show, Eq,Ord)

data PrimitiveTerm
  = ZTerm Z
  | Card  -- ^ cardinality of a set.
  | HGroupTerm -- ^ homology group
  | DTerm -- ^ boundary operator
  | D'Term -- ^ \'inverse\' boundary operator
  | GenTerm GenTerm
  deriving (Show,Eq,Ord)

data GenTerm
  = STerm -- ^ chains
  | CTerm -- ^ cycles
  | TTerm -- ^ cycles, generating homology group
  | HTerm -- ^ homology class
  deriving (Show,Eq,Ord)

zTerm :: Z -> Term
zTerm = PrimitiveTerm . ZTerm

type Failure = String

type E = Either Failure


instance Validable Term where
  valid = error "nyi"

instance Entity Term

type EnvV = M.Map String Term


subst :: EnvV -> Term -> Term
subst vs t = case t of
  Free v -> case M.lookup v vs of
    Just t'  -> subst vs t'
    Nothing ->  t

  Let a s t -> subst vs' t where
    vs' = M.insert a s vs
  
  PrimitiveTerm p -> PrimitiveTerm p

  f :>> x -> subst vs f :>> subst vs x
  a :+> b -> subst vs a :+> subst vs b
  k :!> a -> subst vs k :!> subst vs a


data SomeChain x where
  SomeChain     :: Attestable l => Chain Z l x -> SomeChain x
  SomeChainZero :: Z -> SomeChain x  -- ^ for negative length

spxSomeChain :: (Entity x, Ord x, Attestable l) => Simplex l x -> SomeChain x
spxSomeChain = SomeChain . ch

deriving instance (Entity x, Ord x) => Show (SomeChain x)

instance (Entity x, Ord x) => Eq (SomeChain x) where
  (==) = error "nyi"

instance (Entity x, Ord x) => Ord (SomeChain x) where
  compare = error "nyi"

instance (Entity x, Ord x) => Validable (SomeChain x) where
  valid (SomeChain c)     = valid c
  valid (SomeChainZero z) = valid z

instance (Entity x, Ord x) => Entity (SomeChain x)

instance (Entity x, Ord x) => Fibred (SomeChain x) where
  type Root (SomeChain x) = Z
  root (SomeChain c) = inj $ lengthN $ any c where
    any :: Attestable l => Chain Z l x -> Any l
    any _ = attest

chZero :: (Entity x, Ord x, Attestable l) => Any l -> Chain Z l x
chZero _ = zero ()

instance (Entity x, Ord x) => Additive (SomeChain x) where
  zero l | 0 <= l = case someNatural (prj l) of
                      SomeNatural l' -> SomeChain $ chZero l'
         | 0 > l  = SomeChainZero l

instance Ord AbElement where
  AbElement a `compare` AbElement b = a `compare` b
  
data Value x
  = ZValue Z
  | GenSetValue GenTerm
  | ChainMapValue Z (M.Map Z (SomeChain x))
  | ChainValue Z (SomeChain x)
  | HomologyClassMapValue Z (M.Map Z AbElement)
  | HomologyClassValue Z AbElement
  | HomologyGroupValue Z AbGroup
  deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (Value x) where
  valid = error "nyi"

instance (Entity x, Ord x) => Entity (Value x)

infixr 0 :->
  
data ValueType
  = ZType
  | SomeChainType
  | SomeHomologyClassType
  | ChainType Z
  | HomologyClassType Z
  | HomologyGroupType Z
  | (:->) ValueType ValueType
  deriving (Show, Eq, Ord)


instance Validable ValueType where
  valid t = case t of
    ZType       -> SValid
    _           -> error "nyi"

instance Entity ValueType

instance (Entity x, Ord x) => Fibred (Value x) where
  type Root (Value x) = ValueType
  root v = case v of
    ZValue _                  -> ZType
    GenSetValue t             -> case t of
      HTerm                   -> ZType :-> ZType :-> SomeHomologyClassType
      _                       -> ZType :-> ZType :-> SomeChainType
    ChainMapValue k _         -> ZType :-> ChainType k
    ChainValue k _            -> ChainType k
    HomologyClassMapValue k _ -> ZType :-> HomologyClassType k
    HomologyClassValue k _    -> HomologyClassType k
    HomologyGroupValue k _    -> HomologyGroupType k

instance (Entity x, Ord x) => OrdRoot (Value x)

newtype SumValue x = SumValue (Sum Z (Value x)) deriving (Show,Eq,Ord)

instance (Entity x, Ord x) => Validable (SumValue x) where
  valid (SumValue s) = Label "SumValue" :<=>: valid s

instance (Entity x, Ord x) => Entity (SumValue x)

instance (Entity x, Ord x) => Exposable (SumValue x) where
  type Form (SumValue x) = SumForm Z (Value x)
  form (SumValue s) = form s

instance (Entity x, Ord x) => Fibred (SumValue x) where
  type Root (SumValue x) = ValueType
  root (SumValue s) = root s

svReduce :: (Entity x, Ord x) => SumForm Z (Value x) -> SumForm Z (Value x)
svReduce s = case root s of
  ZType -> case evalZ s of
    Right s' -> S (ZValue s')
    Left _   -> throw $ ImplementationError "svReduce"
  _     -> s


instance (Entity x, Ord x) => Constructable (SumValue x) where
  make = SumValue . make . svReduce

type EnvH n x = M.Map N (SomeHomology n x)

getHomology :: Attestable k => EnvH n x -> Any k -> Maybe (Homology n k x)
getHomology hs k = do
  sh <- lengthN k `M.lookup` hs
  case sh of
    SomeHomology h@(Homology _ _ _ _) -> case eq k h of
      Just Refl -> Just h
      Nothing   -> throw $ ImplementationError "getHomology: inconsitent environment"
  where eq :: (Attestable k, Attestable k') => Any k -> Homology n k' x -> Maybe (k :~: k')
        eq _ _ = eqT 

data Env x where
  Env :: EnvV -> EnvH n x -> Term -> Env x

initEnv :: (Entity x, Ord x, Attestable n) => Regular -> Complex n x -> Env x
initEnv r c = Env (M.empty) mhs (PrimitiveTerm (ZTerm 0)) where
  ChainHomology hs = homology r c
  mhs = M.fromAscList ([0..] `zip` (reverse $ toList hs))

evalFormPrimitive :: EnvH n x -> PrimitiveTerm -> E (SumForm Z (Value x))
evalFormPrimitive hs p = case p of
  ZTerm z   -> return $ S $ ZValue z
  GenTerm t -> return $ S $ GenSetValue t

genSetEmpty :: GenTerm -> Z -> Value x
genSetEmpty t k = case t of
  TTerm -> HomologyClassMapValue k M.empty
  _     -> ChainMapValue k M.empty

genSetChain :: (Entity x, Ord x) => Homology n k x -> Z -> Value x
genSetChain h@(Homology _ _ _ _) k
  = ChainMapValue k $ M.fromAscList ([0..] `zip` (amap1 spxSomeChain $ setxs $ hmgChainSet' h))

genSetCycle :: (Entity x, Ord x) => Homology n k x -> Z -> Value x
genSetCycle h@(Homology _ _ _ _) k
  = ChainMapValue k $ M.fromAscList ([0..] `zip` (amap1 SomeChain $ setxs $ hmgCycleGenSet h))

genSetT :: (Entity x, Ord x) => Homology n k x -> Z -> Value x
genSetT h@(Homology _ _ _ _) k
  = ChainMapValue k $ M.fromAscList ([0..] `zip` (amap1 SomeChain $ setxs $ hmgGroupGenSet h))

genSetMinusOne :: (Entity x, Ord x) => Homology n N0 x -> GenTerm -> Value x
genSetMinusOne h t = ChainMapValue (-1) $ case t of
  STerm -> genS
  CTerm -> genS                         -- d (-1) is zero
  TTerm | lengthN genS' == 0 -> genS    -- d 0 is zero
        | otherwise          -> M.empty -- d 0 is surjective
  
  where genS  = M.fromAscList ([0..] `zip` (amap1 spxSomeChain $ setxs $ hmgChainSet h))
        genS' = hmgChainSet' h
  
evalGenSet :: (Entity x, Ord x) => EnvH n x -> GenTerm -> Z -> Value x
evalGenSet hs t k
  | k == -1 = let Just h0 = getHomology hs W0 in genSetMinusOne h0 t  -- hs is never emtpy.
  | -2 >  k = genSetEmpty t k
  | k >=  0 = case (prj k) `M.lookup` hs of
      Nothing               -> genSetEmpty t k
      Just (SomeHomology h) -> case t of
        STerm               -> genSetChain h k
        CTerm               -> genSetCycle h k
        TTerm               -> genSetT h k

evalChain :: (Entity x, Ord x) => Z -> Maybe (SomeChain x) -> Value x
evalChain k (Just c) = ChainValue k c
evalChain k Nothing  = ChainValue k (zero (k+1)) 

evalFormApplZ :: (Entity x, Ord x) => EnvH n x
  -> SumForm Z (Value x) -> Z -> E (SumForm Z (Value x))
evalFormApplZ hs s z = case s of
  S (GenSetValue t)      -> return $ S $ evalGenSet hs t z
  S (ChainMapValue k cs) -> return $ S $ evalChain k (z `M.lookup` cs)
  _                 -> Left ("not applicable value: " ++ show s)

evalFormAppl :: (Entity x, Ord x) => EnvH n x
  -> SumForm Z (Value x) -> SumForm Z (Value x) -> E (SumForm Z (Value x))
evalFormAppl hs f x = case (root f, root x) of
  (ZType :-> _, ZType) -> evalZ x >>= evalFormApplZ hs f

evalZ :: (Entity x, Ord x) => SumForm Z (Value x) -> E Z
evalZ f = amap1 (foldl (+) 0) $ sequence $ amap1 (uncurry zMlt) $ lcs $ smflc f where
  
  zMlt :: (Entity x, Ord x) => Z -> Value x -> E Z
  zMlt r v = case v of
    ZValue x -> Right (r*x)
    _        -> Left ("not a Z-value: " ++ show v)

-- | pre: all free variables are substitiuted.
--   post: valid SumForm
evalForm :: (Entity x, Ord x) => EnvH n x -> Term -> E (SumForm Z (Value x))
evalForm hs t = case t of
  Free a -> Left ("unbound variable: " ++ a)

  Let v _ _ -> Left ("unresolved \'let\' expresion: " ++ show v)

  a :+> b -> do
    a' <- evalForm hs a
    b' <- evalForm hs b
    case root a' == root b' of
      True  -> return (a' :+ b')
      False -> Left ("not addable: " ++ show (a,b))

  z :!> a -> do
    z' <- evalForm hs z >>= evalZ
    a' <- evalForm hs a
    return (z' :! a')


  PrimitiveTerm p -> evalFormPrimitive hs p

  f :>> x -> do
    f' <- evalForm hs f
    x' <- evalForm hs x
    evalFormAppl hs f' x' 


eval :: (Entity x, Ord x) => Env x -> Term -> E (SumValue x)
eval (Env vs hs itTerm) t
  = evalForm hs (subst vs (Let "it" itTerm t)) >>= return . make

ee :: (Entity x, Ord x) => Env x -> Term -> E (SumForm Z (Value x))
ee (Env vs hs itTerm) t
  = evalForm hs (subst vs (Let "it" itTerm t))

{-
--------------------------------------------------------------------------------
-- version -

version :: String
version ="1.0.0.0"

--------------------------------------------------------------------------------
-- putHelp -

putHelp :: Handle -> IO ()
putHelp hOut = do
  hPutStrLn hOut ""
  hPutStrLn hOut ("Homology Groups " ++ version)
  hPutStrLn hOut ("----------------" ++ (takeN (lengthN version) $ repeat '-'))
  hPutStrLn hOut ""
  hPutStrLn hOut "Exploring interactively the homology of a chain complex:"
  hPutStrLn hOut ""
  hPutStrLn hOut ""
  hPutStrLn hOut "  d (n+1)         d n             d (n-1)     d (k+1)          d k        d 1          d 0"
  hPutStrLn hOut "0 -------> H n n -----> H n (n-1) -------> .. -------> H n k -------> .. -----> H n 0 -----> *"
  hPutStrLn hOut "                                                         ^"
  hPutStrLn hOut "                                                  actual homology"
  hPutStrLn hOut "" 
  hPutStrLn hOut "Commands:"
  hPutStrLn hOut (":q      " ++ "quit")
  hPutStrLn hOut (":help   " ++ "shows this help")
  hPutStrLn hOut (":v      " ++ "validates the actual homology")
  hPutStrLn hOut ""
  hPutStrLn hOut "Operators on the chain complex \'H n\':"
  hPutStrLn hOut ("it             " ++ "the previous result")
  hPutStrLn hOut ("succ           " ++ "the following homology")
  hPutStrLn hOut ("prev           " ++ "the previous homology")
  hPutStrLn hOut ""
  hPutStrLn hOut "Operators on the actual homology \'H n k\':"
  hPutStrLn hOut ("homology group " ++ "the homology group of \'H n k\'.")
  hPutStrLn hOut ("gen chain      " ++ "the set of simplices of lenght k+1, which form the base of")
  hPutStrLn hOut ("               " ++ "the free abelian group of all chains in \'H n k\'.")
  hPutStrLn hOut ("gen cycle      " ++ "a sub set of all chains, which generate the sub group of all")
  hPutStrLn hOut ("               " ++ "cycles in the group of all chains.")
  hPutStrLn hOut ("gen class      " ++ "a sub set of all cycles, such that there homology class generate")
  hPutStrLn hOut ("               " ++ "the homology group of \'H n k\'.")
  hPutStrLn hOut ("card chain     " ++ "the cardinality of \'gen chain\'.")
  hPutStrLn hOut ("card cycle     " ++ "the cardinality of \'gen cycle\'.")
  hPutStrLn hOut ("card class     " ++ "the cardinality of \'gen class\'.")
  hPutStrLn hOut ("s<i>           " ++ "the i-the element of the set \'gen chain\'.")
  hPutStrLn hOut ("               " ++ "Example: s7 is the 7-th element.")
  hPutStrLn hOut ("c<i>           " ++ "the i-the element of the set \'gen cycle\'.")
  hPutStrLn hOut ("h<i>           " ++ "the i-the element of the set \'gen class\'.")
  hPutStrLn hOut ("sum <ls>       " ++ "the sum of the linear combination \'ls\' of elements in \'gen\' and coefficients in Z.")
  hPutStrLn hOut ("               " ++ "Example: lc s3+4!s8-c5+h0. (\'!\' denotes the scalar multiplication)")
  

  
--------------------------------------------------------------------------------
-- Command -

data Command
  = Identity
  | Quit
  | Help
  | ValidActual
  | Operator Operator

--------------------------------------------------------------------------------
-- Operator -

data Operator
  = It
  | Succ
  | Prev
  | Eval Function [Argument]

--------------------------------------------------------------------------------
-- Function -

data Function
  = FHomology
  | FGen
  | FCard
  | FSum

--------------------------------------------------------------------------------
-- Index -

data Index = Index Char N

--------------------------------------------------------------------------------
-- Argumant -

data Argument
  = AGroup
  | AChain
  | ACycle
  | AClass
  | ASumForm (SumForm Z Index)

--------------------------------------------------------------------------------
-- Result -

data Result where
  Non           :: Result
  HomologyGroup :: AbGroup -> Result
  Cardinality   :: N -> Result
  Generator     :: (Entity x, Ord x) => Set (Chain Z (k+1) x) -> Result
  Chain         :: (Entity x, Ord x) => Chain Z (k+1) x -> Result

--------------------------------------------------------------------------------
-- Failure -

type Failure = String

--------------------------------------------------------------------------------
-- Operand -

data Operand where 
  Operand :: (Entity x, Ord x, Attestable n)
    => N -- ^ the dimension of the homologies.
    -> (SomeHomology n x,N) -- ^ the actual homology.
    -> [(SomeHomology n x,N)] -- ^ the succesive homologies.
    -> [(SomeHomology n x,N)] -- ^ the previos homologies.
    -> Result 
    -> Operand

--------------------------------------------------------------------------------
-- opdIt -

opdIt :: Operand -> Result
opdIt (Operand _ _ _ _ it) = it

--------------------------------------------------------------------------------
-- prpActualHomology -

-- | validation of the actual homology.
prpActualHomology :: Operand -> Statement
prpActualHomology (Operand n (SomeHomology (Homology n' k' _ _),k) _ _ _) = Prp "ActualHomology" :<=>:
  And [ Label "dimension" :<=>: valid n
      , Label "actual homology" :<=>: And
          [ Label "k <= n" :<=>: (k <= n) :?> Params ["n":=show n, "k":=show k]
          , Label "dimensons correspondence" :<=>: And
             [ Label "n" :<=>: (lengthN n' == n) :?> Params ["n'":= show n', "n":=show n]
             , Label "k" :<=>: (lengthN k' == k) :?> Params ["k'":= show k', "k":=show k]
             ]
          ]
      ]

--------------------------------------------------------------------------------
-- validateActual -

-- | validates the actual homology.
validateActual :: Handle -> Handle -> Operand -> IO ()
validateActual hOut hErr hks = do
    v <- validate $ prpActualHomology hks
    hPutStrLn hOut ("validation result: " ++ show v)
  `catch` algException
  where
    algException :: AlgebraicException -> IO ()
    algException _ = return ()

--------------------------------------------------------------------------------
-- initOperand -

-- | initialising an operand.
initOperand :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> Operand
initOperand r c = Operand n h0 hks [] Non where
  n = lengthN $ cpxDim c
  ChainHomology hs = homology r c
  -- note: hs is not empty!
  h0:hks = (reverse $ toList hs) `zip` [0..]

--------------------------------------------------------------------------------
-- nextWord -

nextWord :: String -> IO (String,String)
nextWord str = return (w,dropWhile isSpace str') where
  (w,str') = span (not . isSpace) $ dropWhile isSpace str

--------------------------------------------------------------------------------
-- parseCCC -

parseCCC :: String -> IO (Maybe Argument)
parseCCC str = do
  ws <- nextWord str
  case ws of
    ("chain","") -> return $ Just AChain
    ("cycle","") -> return $ Just ACycle
    ("class","") -> return $ Just AClass
    _            -> return Nothing
    

--------------------------------------------------------------------------------
-- parseCommand -

parseCommand ::  String -> IO (Maybe Command)
parseCommand str = do
  ws <- nextWord str
  case ws of
    -- commands
    ("","")      -> return $ Just Identity
    (":q","")    -> return $ Just Quit
    (":help","") -> return $ Just Help
    (":v","")    -> return $ Just ValidActual

    -- operators
    ("it","")    -> return $ Just $ Operator It
    ("succ","")  -> return $ Just $ Operator Succ
    ("prev","")  -> return $ Just $ Operator Prev
    ("homology",str') -> do
      ws <- nextWord str'
      case ws of
        ("group","") -> return $ Just $ Operator $ Eval FHomology [AGroup]
        _            -> return Nothing
    ("gen",str') -> do
      mc <- parseCCC str'
      case mc of
        Just c -> return $ Just $ Operator $ Eval FGen [c]
        _      -> return Nothing
    ("card",str') -> do
      mc <- parseCCC str'
      case mc of
        Just c -> return $ Just $ Operator $ Eval FCard [c]
        _      -> return Nothing
{-        
    ("sum",str') -> do
      mc <- parseLinearCombination str'
      case mc of
        Just lc -> error "nyi"
-}
    _  -> return Nothing

--------------------------------------------------------------------------------
-- getCommand -

getCommand :: Handle -> Handle -> Handle
  -> Operand -> IO (Maybe Command)
getCommand hIn hOut hErr (Operand n (_,k) _ _ _) = do
  hFlush hOut
  hPutStr hOut ("H " ++ show n ++ " " ++ show k ++ "> ")
  ln <- hGetLine hIn
  parseCommand ln

--------------------------------------------------------------------------------
-- evalSucc -

evalSucc :: Operand -> IO (Either Failure Operand)
evalSucc (Operand _ _ [] _ _)
  = return $ Left "there is no further homology!"
evalSucc (Operand n h (h':hSuccs)  hPrevs it)
  = return $ Right $ Operand n h' hSuccs (h:hPrevs) it

--------------------------------------------------------------------------------
-- evalPrev -

evalPrev :: Operand -> IO (Either Failure Operand)
evalPrev (Operand _ _ _ [] _)
  = return $ Left "there is now previous homology!"
evalPrev (Operand n h hSuccs (h':hPrevs) it)
  = return $ Right $ Operand n h' (h:hSuccs) hPrevs it

--------------------------------------------------------------------------------
-- evalHomologyGroup -

evalHomologyGroup :: Operand -> IO (Either Failure Operand)
evalHomologyGroup (Operand n sh@(SomeHomology h,_)  hSucc hPrev _)
  = return $ Right $ Operand n sh hSucc hPrev it where
  it = HomologyGroup $ hmgGroup h

--------------------------------------------------------------------------------
-- evalCardChain -

evalCardChain :: Operand -> IO (Either Failure Operand)
evalCardChain (Operand n sh@(SomeHomology h,_)  hSucc hPrev _)
  = return $ Right $ Operand n sh hSucc hPrev it where
  it = Cardinality $ lengthN $ hmgChainSet' h

--------------------------------------------------------------------------------
-- evalGen -

evalGen :: Argument -> Operand -> IO (Either Failure Operand)
evalGen arg (Operand k sh@(SomeHomology h@(Homology _ _ _ _),_)  hSucc hPrev _) = case arg of
  AChain -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ set $ amap1 ch $ setxs $ hmgChainSet' h
  ACycle -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ hmgCycleGenSet h
  AClass -> return $ Right $ Operand k sh hSucc hPrev it where
    it = Generator $ hmgGroupGenSet h
  _      -> return $ Left "unknown argument for \'gen\'"

--------------------------------------------------------------------------------
-- evalCard -

evalCard :: Argument -> Operand -> IO (Either Failure Operand)
evalCard arg hks = do
  mhks' <- evalGen arg hks
  case mhks' of
    Right (Operand k h hs hp (Generator gs)) -> return $ Right (Operand k h hs hp it) where
      it = Cardinality $ lengthN gs
    Right _ -> throw $ ImplementationError "evalCard"
    f      -> return f
    
--------------------------------------------------------------------------------
-- eval -

eval :: Operator -> Operand -> IO (Either Failure Operand)
eval opr hks = case opr of
  It      -> return $ Right hks
  Succ    -> evalSucc hks
  Prev    -> evalPrev hks
  Eval FHomology [AGroup] -> evalHomologyGroup hks
  Eval FGen [arg]         -> evalGen arg hks 
  Eval FCard [arg]        -> evalCard arg hks
  _  -> return $ Left "unknown operator"                      

--------------------------------------------------------------------------------
-- putFailure -

putFailure :: Handle -> Failure -> IO ()
putFailure hErr msg = do
  hPutStrLn hErr ("!!!Failure: " ++ msg)

--------------------------------------------------------------------------------
-- putResult -

putResult :: Handle -> Result -> IO ()
putResult hOut res = case res of
  Non             -> return ()
  HomologyGroup h -> hPutStrLn hOut $ show h
  Cardinality c   -> hPutStrLn hOut $ show c
  Generator gs    -> hPutStrLn hOut $ show gs
  Chain c         -> hPutStrLn hOut $ show c

--------------------------------------------------------------------------------
-- iComplex -

-- | intaractive modus for a complex according to the standard handles.
iComplex :: (Entity x, Ord x, Attestable n)
  => Regular -> Complex n x -> IO ()
iComplex = iComplex' stdin stdout stderr

  -- | intaractive modus for a complex.
iComplex' :: (Entity x, Ord x, Attestable n)
  => Handle -> Handle -> Handle
  -> Regular -> Complex n x -> IO ()
iComplex' hIn hOut hErr r c = rep hks where
  hks = initOperand r c

  rep :: Operand -> IO ()
  rep hks = do
    mcmd <- getCommand hIn hOut hErr hks
    case mcmd of
      Just Identity -> rep hks
      Just Quit     -> return ()
      Just Help     -> do
        putHelp hOut
        rep hks
      Just ValidActual -> do
        validateActual hOut hErr hks
        rep hks
      Just (Operator opr)  -> do
        res <- eval opr hks
        case res of
          Right hks' -> do
            putResult hOut $ opdIt hks'
            rep hks'
          Left err   -> do
            putFailure hErr err
            rep hks
      Nothing -> do
        hPutStrLn hOut "!!!unknown command"
        rep hks

-}
