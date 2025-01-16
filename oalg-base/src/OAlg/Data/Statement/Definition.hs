
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

-- |
-- Module      : OAlg.Data.Statement.Definition
-- Description : definition of statements on properties
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Statements on properties which can be validated via 'validateStoch'. They serve to
-- implement automatic testing (see "OAlg.Control.Validate").
-- 
-- __Examples__ Deterministic
-- 
-- Validation of the valid and invalid statement
-- 
-- >>> getOmega >>= validateStoch SValid 10
-- Valid
-- 
-- >>> getOmega >>= validateStoch SInvalid 5
-- Invalid
-- 
-- As no stochastic was used to evaluate the two examples, the result is 'Valid' and 'Invalid'
-- respectively!
-- 
-- __Examples__ Stochastic
-- 
-- Validation of a 'Forall' and 'Exist' statement
-- 
-- >>> getOmega >>= validateStoch (Forall (xIntB 0 10) (\i -> (0 <= i && i <= 10):?>Params["i":=show i]-- )) 100
-- ProbablyValid
-- 
-- >>> getOmega >>= validateStoch (Exist (xIntB 0 10) (\i -> (11 <= i):?>Params["i":=show i])) 100
-- ProbablyInvalid
-- 
-- The valuation of these two examples uses the given 'Omega' and 'Wide' of @100@ to pick randomly
-- @100@ samples of the given random variable @'xIntB' 0 10@ and applies these samples to the given
-- test function. The result is 'ProbablyValid' and 'ProbablyInvalid' respectively!
module OAlg.Data.Statement.Definition
  (
    -- * Statement
    Statement(..),(.==.), (./=.),(|~>), someException
  , Label(Label,Prp), Message(..), Variable, Parameter(..)


    -- * Validating
    -- ** Stochastic
  , validateStoch, Wide, value, V(), valDeterministic, valT, T, Valid(..)
  , showV, indent0, showVStatement

    -- ** Deterministic
  , validateDet
  
    -- * Reducing Values
  , tests, SPath, cntTests
  , rdcTrue, cntTestsRdcTrue
  , rdcFalse, cntTestsRdcFalse
  , rdcDndPrms, cntTestsRdcDndPrms
  , rdcFailed, cntTestsRdcFailed

    -- * X
  , xValue, xWO, xValid

    -- * Exception
  , ValidateingException(..)
  )
  where

import Prelude (Num(..),Bounded(..))

import Control.Monad
import Control.Exception
import Control.DeepSeq

import System.IO.Unsafe
import System.IO

import Data.List (map,(++),take,zip)
import Data.Foldable hiding (and)

import OAlg.Category.Definition

import OAlg.Control.Exception
import OAlg.Control.HNFData
import OAlg.Control.Verbose

import OAlg.Data.Logical
import OAlg.Data.Boolean.Definition
import OAlg.Data.Ord
import OAlg.Data.Equal
import OAlg.Data.X
import OAlg.Data.Show 
import OAlg.Data.Maybe
import OAlg.Data.Canonical
import OAlg.Data.Number

--------------------------------------------------------------------------------
-- ValidateingException -

-- | validating exceptions which are sub exceptions from 'SomeOAlgException'.
data ValidateingException
  = NonDeterministic
  deriving (Eq,Show)

instance Exception ValidateingException where
  toException   = oalgExceptionToException
  fromException = oalgExceptionFromException

--------------------------------------------------------------------------------
-- Label -

-- if you add or change the internal Labels, you need to adappt relevantLabel!
-- | a labels.
data Label
  = Label String
  | Prp String

    -- internal
  | Prms -- premises
  | Cncl -- conclusion

instance Show Label where
  show l = case l of
    Label s -> "(" ++ s ++ ")"
    Prp p   -> "prp" ++ p
    Prms    -> "premise"
    Cncl    -> "conclusion"

instance Verbose Label

--------------------------------------------------------------------------------
-- Variable -

-- | type of variables.
type Variable = String

--------------------------------------------------------------------------------
-- Parameter -

-- | showing the involved parameters of a statement.
data Parameter where
  (:=) :: Variable -> String -> Parameter

deriving instance Show Parameter

instance Verbose Parameter where
  vshow v (var := x) = jtween " " [var,":=",vshowStr (mnString v) x] 

--------------------------------------------------------------------------------
-- Message -

-- | a message.
data Message
  = MInvalid -- ^ used for relations where no further information is desired or possible to give (see @relRelation@ as an example). 
  | Message String -- ^ a message
  | Params [Parameter] -- ^ a list of parameters
  deriving (Show)

instance Verbose Message where
  vshow v (Message m  ) = vshowStr (mnString v) m 
  vshow v (Params ps)   = vshow v ps
  vshow _ m             = show m

--------------------------------------------------------------------------------
-- Statement -

infix  4 :?>, .==., ./=.
infixr 3 :&&
infixr 2 :||
infixr 1 :=>, :<=>
infixr 0 :<=>:

-- | statement on properties..
data Statement where
  
  -- | the invalid statement.
  SInvalid :: Statement

  -- | the valid statement.
  SValid   :: Statement

  -- | checking a boolean.
  (:?>)    :: Bool -> Message -> Statement

  -- | catching an exception.
  Catch    :: Exception e => Statement -> (e -> Statement) -> Statement

  -- | not
  Not      :: Statement -> Statement

  -- | and
  (:&&)    :: Statement -> Statement -> Statement

  -- | and
  And      :: [Statement] -> Statement

  -- | or
  (:||)    :: Statement -> Statement -> Statement

  -- | or
  Or       :: [Statement] -> Statement

  -- | implication
  (:=>)    :: Statement -> Statement -> Statement

  -- | implication
  Impl     :: [Statement] -> Statement -> Statement

  -- | efinitional equivalence
  (:<=>:)  :: Label -> Statement -> Statement

  -- | equivalence
  (:<=>)   :: Statement -> Statement -> Statement

  -- | equivalence
  Eqvl     :: [Statement] -> Statement

  -- | the for all constructor
  Forall   :: X x -> (x -> Statement) -> Statement

  -- | the exist constructor.
  Exist    :: X x -> (x -> Statement) -> Statement

instance Logical Statement where
  (||)  = (:||)
  (&&)  = (:&&)
  
instance Boolean Statement where
  false = SInvalid
  true  = SValid
  not   = Not
  or    = Or
  and   = And
  (~>)  = (:=>)
  eqvl  = Eqvl

instance HNFData Statement where
  rhnf p = case p of
             SInvalid -> ()
             _      -> ()

--------------------------------------------------------------------------------
-- someException -

-- | convenient catcher for 'SomeException'.
someException :: Statement -> SomeException -> Statement
someException p _ = p

--------------------------------------------------------------------------------
-- (.==.) -

-- | checking for equality.
(.==.) :: Eq a => a -> a -> Statement
a .==. b = (a == b) :?> MInvalid

--------------------------------------------------------------------------------
-- (./=.) -

-- | checking for inequality.
(./=.) :: Eq a => a -> a -> Statement
a ./=. b = (a /= b) :?> MInvalid

--------------------------------------------------------------------------------
-- (|~>) -

infixr 1 |~>

-- | implication without resulting in denied premises for a 'false' premises. This
--   is useful for /switch/ cases.
(|~>) :: Statement -> Statement -> Statement
a |~> b = Not a || b 
        
--------------------------------------------------------------------------------
-- Valid -

-- | weak form of classical boolean values arising from stochastically performed valuation
--   of 'Statement's.
--
--  __Definition__ Let @a@, @b@ be in 'Valid', then we define:
--
--  (1) @'not' a = 'toEnum' ('fromEnum' 'Valid' '-' 'fromEnum' a)@.
--
--  (1) @a '||' b = max a b@.
--
--  (1) @a '&&' b = min a b@.
--
--  (1) @a '~>' b = 'not' a '||' b@.
--
--  __Note__ @min@ and @max@ are implemented lazy as 'Valid' is bounded. This
--  is important that '~>' behaves as desired, i.e. for @a '~>' b@ and @a = 'Invalid'@ then
--  @b@ has not to be evaluated, because the maximum is already reached..
data Valid = Invalid | ProbablyInvalid | ProbablyValid | Valid
  deriving (Show,Eq,Ord,Enum,Bounded)

instance NFData Valid where
  rnf Invalid = ()
  rnf _       = ()

instance Logical Valid where
  a || b  | a == Valid = a -- to make (||) in its first argument lazy
          | otherwise  = case a `compare`b of
                           GT -> a
                           _  -> b
  a && b  | a == Invalid = a -- to make (&&) in its first argument lazy
          | otherwise   = case a `compare` b of
                            LT -> a
                            _  -> b
  
instance Boolean Valid where
  false = Invalid
  true  = Valid
  not t = toEnum (fromEnum Valid - fromEnum t)

instance Projectible Bool Valid where
  prj Valid            = True
  prj ProbablyValid    = True
  prj ProbablyInvalid  = False
  prj Invalid          = False

--------------------------------------------------------------------------------
-- xValid -

-- | uniformly distributed random variable of 'Valid'.
xValid :: X Valid
xValid = xEnum

--------------------------------------------------------------------------------
-- T -

-- | the /truth/ type of a value @v@.
type T = HNFValue Valid

--------------------------------------------------------------------------------
-- V -

-- | the 'value' of a statement resulting from its validation.  'Forall' and 'Exist' are resolved
-- by finite samples.
data V
  = V Valid
  | forall e . Exception e => VFailure e
  | VCheck T (Maybe Message)
  | VCatch T (Maybe V) V -- Just v has been catched
  | VNot T V
  | VAnd T [V]    
  | VOr T [V]  
  | VImpl T V
  | VDefEqvl Label T V
  | VEqvl T V
  | VForall T V
  | VExist T V

deriving instance Show V
instance Verbose V

--------------------------------------------------------------------------------
-- Indent -

-- | indentation, where the first component is the basic indentation and the second the actual.
type Indent = (String,String)

-- | the next deeper indentation.
isucc :: Indent -> Indent
isucc (i,is) = (i,i++is)

-- | the indentation as string.
indent :: Indent -> String
indent = snd

-- | the initial indentation given by a indentation string.
indent0 :: String -> Indent
indent0 i = (i,"")

--------------------------------------------------------------------------------
-- showIndent -

showIndent :: Indent -> String -> String
showIndent is ss = ind ss where
  ind []        = []
  ind ('\n':ss) = "\n" ++ indent is ++ ind ss
  ind (s:ss)    = s:ind ss
  
--------------------------------------------------------------------------------
-- showException -

showException :: Exception e => Indent -> e -> String
showException is e = showIndent is (show e) ++ "\n"

--------------------------------------------------------------------------------
-- showValid -

showValid :: Indent -> Valid -> String
showValid is v = indent is ++ show v ++ "\n"

--------------------------------------------------------------------------------
-- showFailure -

showFailure :: Exception e => Indent -> e -> String
showFailure is e = indent is ++ "failure " ++ showException (isucc is) e

--------------------------------------------------------------------------------
-- showTLeaf -

showTLeaf :: Indent -> T -> String
showTLeaf is (HNFValue b) = showValid is b
showTLeaf is (Failure e)  = showFailure is e

--------------------------------------------------------------------------------
-- showTNode -

showTNode :: T -> String
showTNode (HNFValue b) = show b
showTNode (Failure e)  = show e

--------------------------------------------------------------------------------
-- showParams -

showParams :: Indent -> [Parameter] -> String
showParams _ [] = ""
showParams is ((v := p):ps)
  =  indent is ++ v
  ++ " := "
  ++ showIndent (isucc is) p ++ "\n" ++ showParams is ps

--------------------------------------------------------------------------------
-- showMessage -

showMessage :: Indent -> Message -> String
showMessage is m = case m of
  MInvalid    -> ""
  Message s -> indent is ++ "message: " ++ s ++ "\n"
  Params ps -> indent is ++ "parameters" ++ "\n" ++ showParams (isucc is) ps

--------------------------------------------------------------------------------
-- showMaybeMessage -

showMaybeMessage :: Indent -> Maybe Message -> String
showMaybeMessage _ Nothing   = ""
showMaybeMessage is (Just m) = showMessage is m

--------------------------------------------------------------------------------
-- showCheck -

showCheck :: Indent -> T -> (Maybe Message) -> String
showCheck is t m =  indent is ++ "check " ++ showTNode t ++ "\n"
                 ++ showTLeaf is' t
                 ++ showMaybeMessage is' m
  where is' = isucc is

--------------------------------------------------------------------------------
-- showCatched -

showCatched :: Indent -> V -> String
showCatched is v = indent is ++ "catched" ++ "\n" ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showCatchSubs -

showCatchSubs :: Indent -> V -> String
showCatchSubs is v = indent is ++ "substitution" ++ "\n" ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showCatch -

showCatch :: Indent -> T -> Maybe V -> V -> String
showCatch is _ Nothing v  = showV is v
showCatch is t (Just c) v = indent is ++ "catch " ++ showTNode t ++ "\n"
                          ++ showCatched is' c
                          ++ showCatchSubs is' v
  where is' = isucc is

--------------------------------------------------------------------------------
-- showNot -

showNot :: Indent -> T -> V -> String
showNot is t v = indent is ++ "not " ++ showTNode t ++ "\n" ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showVs -

showVs :: Indent -> [V] -> String
showVs _ []      = ""
showVs is (v:vs) = showV is v ++ showVs is vs

--------------------------------------------------------------------------------
-- showAnd -

showAnd :: Indent -> T -> [V] -> String
showAnd is t vs = indent is ++ "and " ++ showTNode t ++ "\n"
                ++ showVs (isucc is) vs

--------------------------------------------------------------------------------
-- showOr -

showOr :: Indent -> T -> [V] -> String
showOr is t vs = indent is ++ "or " ++ showTNode t ++ "\n"
                ++ showVs (isucc is) vs

--------------------------------------------------------------------------------
-- showImpl -

showImpl :: Indent -> T -> V -> String
showImpl is t v = indent is ++ "=> " ++ showTNode t ++ "\n"
                ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showDefEqvl -

showDefEqvl :: Indent -> Label -> T -> V -> String
showDefEqvl is l t v = indent is ++ show l ++ " " ++ showTNode t ++ "\n"
                     ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showEqvl -

showEqvl :: Indent -> T -> V -> String
showEqvl is t v = indent is ++ "<=> " ++ showTNode t ++ "\n"
                ++ showV (isucc is) v
--------------------------------------------------------------------------------
-- showForall -

showForall :: Indent -> T -> V -> String
showForall is t v = indent is ++ "for all " ++ showTNode t ++ "\n"
                  ++ showV (isucc is) v

--------------------------------------------------------------------------------
-- showExist -

showExist :: Indent -> T -> V -> String
showExist is t v = indent is ++ "exist " ++ showTNode t ++ "\n"
                 ++ showV (isucc is) v
                 
--------------------------------------------------------------------------------
-- showV -

-- | pretty showing a value with the given indentation.
showV :: Indent -> V -> String
showV is v = case v of
  V b            -> showValid is b
  VFailure e     -> showFailure is e
  VCatch t mv v  -> showCatch is t mv v
  VCheck t m     -> showCheck is t m
  VNot t v'      -> showNot is t v'
  VAnd t vs      -> showAnd is t vs
  VOr t vs       -> showOr is t vs
  VImpl t v      -> showImpl is t v
  VDefEqvl l t v -> showDefEqvl is l t v
  VEqvl t v      -> showEqvl is t v
  VForall t v    -> showForall is t v
  VExist t v     -> showExist is t v


--------------------------------------------------------------------------------

-- | determines whether the value is deterministic, i.e. dose not contain a 'VForall'
--   or 'VExist' constructor.
valDeterministic :: V -> Bool
valDeterministic v = case v of
  VForall _ (VAnd _ []) -> True
  VForall _ _           -> False
  VExist _ (VOr _ [])   -> True
  VExist _ _            -> False
  VCatch _ Nothing v    -> valDeterministic v
  VCatch _ (Just v) w   -> and $ map valDeterministic [v,w]
  VNot _ v              -> valDeterministic v
  VAnd _ vs             -> and $ map valDeterministic vs
  VOr _ vs              -> and $ map valDeterministic vs
  VImpl _ v             -> valDeterministic v
  VDefEqvl _ _ v        -> valDeterministic v
  VEqvl _ v             -> valDeterministic v
  _                     -> True

--------------------------------------------------------------------------------
-- valT -

-- | validating a value @v@.
valT :: V -> T
valT v = case v of
  V t              -> HNFValue t
  VFailure e       -> Failure e
  VCheck t _       -> t
  VCatch t _ _     -> t
  VNot t _         -> t
  VAnd t _         -> t
  VOr t _          -> t
  VImpl t _        -> t
  VDefEqvl _ t _   -> t
  VEqvl t _        -> t
  VForall t _      -> t
  VExist t _       -> t

--------------------------------------------------------------------------------
-- Wide -

-- | the wide for a 'Forall' and 'Exist' resolution.
type Wide = Int

--------------------------------------------------------------------------------
-- value -

-- | evaluates the value of a statement according a given 'Wide' and 'Omega'.
--
--  __Note__
--
--  (1) The only reason to valuate a statement in the 'IO' monad is
--  to be able to catch exceptions. Other interactions with the /real world/ during
--  the valuation are not performed.
--
--  (2) During the evaluation process the given wide and omega will not be changed and as
--  such all /same/ random variables will produce exactly the same samples. This restricts
--  the stochastic, but it is necessary for the sound behavior of the validation of statements.
value :: Statement -> Wide -> Omega -> IO V
value p w o = do
  hfp <- hnfValue p
  case hfp of
    Failure e  -> return (VFailure e)
    HNFValue p -> val p w o
  where
    val p w o = case p of
      SInvalid     -> return $ V Invalid
      SValid       -> return $ V Valid
      b :?> m      -> valCheck b m
      Catch p h    -> valCatch p h w o
      Not p        -> valNot p w o
      a :&& b      -> valAnd [a,b] w o
      And ps       -> valAnd ps w o
      a :|| b      -> valOr [a,b] w o
      Or ps        -> valOr ps w o
      a :=> b      -> valImpl [a] b w o
      Impl as b    -> valImpl as b w o
      l :<=>: p    -> valDefEqvl l p w o
      a :<=> b     -> valEqvl [a,b] w o
      Eqvl as      -> valEqvl as w o
      Forall x px  -> valForall x px w o
      Exist x px   -> valExist x px w o

----------------------------------------
-- valCheck -

valCheck :: Bool -> Message -> IO V
valCheck b m = do
  hfb <- hnfValue b
  case hfb of
    Failure e -> return $ VCheck (Failure e) Nothing
    HNFValue b -> return $ case b of
      True    -> VCheck (HNFValue Valid) Nothing
      False   -> VCheck (HNFValue Invalid) (Just m)

----------------------------------------
-- valCatch -

valCatch :: Exception e => Statement -> (e -> Statement) -> Wide -> Omega -> IO V
valCatch p h w o = do
  v <- value p w o
  case valT v of
    Failure s -> case castException h s of
                   Nothing -> return $ VCatch (Failure s) Nothing v
                   Just e  -> do
                     v' <- value (h e) w o
                     return $ VCatch (valT v') (Just v) v' 
    t         -> return $ VCatch t Nothing v

  where castException :: (Exception s,Exception e) => (e -> x) -> s -> Maybe e
        castException _ s = fromException $ toException s

----------------------------------------
-- valNot -

valNot :: Statement -> Wide -> Omega -> IO V
valNot p w o = do
  v <- value p w o
  case valT v of
    Failure e  -> return $ VNot (Failure e) v
    HNFValue t -> return $ VNot (HNFValue (not t)) v

----------------------------------------
-- valAnd -

valAnd :: [Statement] -> Wide -> Omega -> IO V
valAnd ps w o = do
  hfps <- hnfValue ps
  case hfps of
    Failure e   -> return $ VAnd (Failure e) []
    HNFValue ps -> allTrue Valid ps []
  where allTrue s [] vs                    = return $ VAnd (HNFValue s) vs
        allTrue s _ vs | s < ProbablyValid = return $ VAnd (HNFValue s) vs  
        allTrue s (p:ps) vs                = do
          v <- value p w o 
          case valT v of
            HNFValue t -> allTrue (s&&t) ps (v:vs)
            f          -> return $ VAnd f (v:vs)

----------------------------------------
-- valOr -

valOr :: [Statement] -> Wide -> Omega -> IO V
valOr ps w o = do
  hfps <- hnfValue ps
  case hfps of
    Failure e  -> return $ VOr (Failure e) []
    HNFValue ps -> existTrue Invalid ps []
  where existTrue s [] vs                      = return $ VOr (HNFValue s) vs
        existTrue s _ vs | s > ProbablyInvalid = return $ VOr (HNFValue s) vs
        existTrue s (p:ps) vs                  = do
          v <- value p w o
          case valT v of
            HNFValue t -> existTrue (s||t) ps (v:vs)
            f          -> return $ VOr f (v:vs)

----------------------------------------
-- valImpl -

valImpl :: [Statement] -> Statement -> Wide -> Omega -> IO V
valImpl pms cn w o = do
  v <- value (Or [Not (Prms:<=>:(And pms)),(Cncl:<=>:cn)]) w o
  return $ VImpl (valT v) v 

----------------------------------------
-- valDefEqvl -

valDefEqvl :: Label -> Statement -> Wide -> Omega -> IO V
valDefEqvl l p w o = do
  v <- value p w o
  return $ VDefEqvl l (valT v) v

----------------------------------------
-- valEqvl -

valEqvl :: [Statement] -> Wide -> Omega -> IO V
valEqvl [] _ _     = return $ V Valid
valEqvl (a:as) w o = do
  v <- value (And impls) w o
  return $ VEqvl (valT v) v
  where impls = map (uncurry (:=>)) $ zip (a:as) (as++[a])

----------------------------------------
-- valForall -

valForall :: X x -> (x -> Statement) -> Wide -> Omega -> IO V
valForall x p w o = do
  v <- value (And ps) w o
  case v of
    VAnd t [] -> return $ VForall t v
    _         -> return $ VForall (fmap (ProbablyValid&&) $ valT v) v
  where ps = map p $ take w $ samples x o

----------------------------------------
-- valExist -
valExist :: X x -> (x -> Statement) -> Wide -> Omega -> IO V
valExist x p w o = do
  v <- value (Or ps) w o
  case v of
    VOr t [] -> return $ VExist t v
    _        -> return $ VExist (fmap (ProbablyInvalid||) $ valT v) v
  where ps = map p $ take w $ samples x o


--------------------------------------------------------------------------------
-- validateStoch -

-- | validates the statement according to a given 'Wide' and 'Omega'. For
--   deterministic statements better use 'validateDet' and for non deterministic
--   or to get more information 'OAlg.Control.Validate.validate'.
validateStoch :: Statement -> Wide -> Omega -> IO Valid
validateStoch p w o = fmap (fromHNFValue . valT) $ value p w o

--------------------------------------------------------------------------------
-- validateDet -

-- | validation for /deterministic/ statements.
--
--  __Definition__ A statement s is called __/deterministic/__ if and only if it dose not depend
--  on the stochastic nor on the state of the machine.
--
-- __Examples__
--
-- >>> validateDet SValid
-- True
--
-- >>> validateDet (Forall xBool (\_ -> SValid))
-- *** Exception: NonDeterministic
--
-- >>> validateDet (SValid || Exist xInt (\i -> (i==0):?>MInvalid))
-- True
validateDet :: Statement -> Bool
validateDet p = unsafePerformIO $ do
  v <- value p (throw NonDeterministic) (throw NonDeterministic)
  case valT v of
    Failure e  -> throw e
    HNFValue s -> case s of
      Valid    -> return True
      Invalid  -> return False
      st       -> throw $ ImplementationError
                    $ ("deterministic statement with " ++ show st)

--------------------------------------------------------------------------------
-- isTrueT -

-- | checking for being 'True'.
isTrueT :: T -> Bool
isTrueT (HNFValue sb ) = ProbablyValid <= sb
isTrueT _              = False

--------------------------------------------------------------------------------
-- rdcTrue -

-- | reduces true valus to its relevant part.
rdcTrue :: V -> Maybe V
rdcTrue v | not $ isTrueT $ valT v = Nothing
rdcTrue v = case v of
  V _             -> return v
  VCheck _ _      -> return v
  VCatch t e v'   -> rdcTrue v' >>= return . VCatch t e
  VNot t v'       -> rdcFalse v' >>= return . VNot t 
  VAnd t vs       -> (sequence $ map rdcTrue vs) >>= return . VAnd t
  VOr t (v':_)    -> rdcTrue v' >>= return . VOr t . return 
  VImpl t v'      -> rdcTrue v' >>= return . VImpl t
  VEqvl t v'      -> rdcTrue v' >>= return . VEqvl t
  VDefEqvl l t v' -> rdcTrue v' >>= return . VDefEqvl l t
  VForall t v'    -> rdcTrue v' >>= return . VForall t
  VExist t v'     -> rdcTrue v' >>= return . VExist t
  _               -> Nothing

--------------------------------------------------------------------------------
-- rdcFalse -

-- | checking for being 'False'.
isFalseT :: T -> Bool
isFalseT (HNFValue sb) = sb < ProbablyValid
isFalseT _             = False

-- | reduces false valus to its relevant part.
rdcFalse :: V -> Maybe V
rdcFalse v | not $ isFalseT $ valT v = Nothing
rdcFalse v = case v of
  V _             -> return v
  VCheck _ _      -> return v
  VCatch t e v'   -> rdcFalse v' >>= return . VCatch t e
  VNot t v'       -> rdcTrue v' >>= return . VNot t
  VAnd t (v':_)   -> rdcFalse v' >>= return . VAnd t . return
  VOr t vs        -> (sequence $ map rdcFalse vs) >>= return . VOr t
  VImpl t v'      -> rdcFalse v' >>= return . VImpl t 
  VEqvl t v'      -> rdcFalse v' >>= return . VEqvl t
  VDefEqvl l t v' -> rdcFalse v' >>= return . VDefEqvl l t
  VForall t v'    -> rdcFalse v' >>= return . VForall t
  VExist t v'     -> rdcFalse v' >>= return . VExist t
  _               -> Nothing

--------------------------------------------------------------------------------
-- rdcDndPrms -

-- | gets the conclusion - if there is - of a true implication.
--
--   pre: v is true implication
getCncl :: V -> Maybe V
getCncl (VImpl (HNFValue Valid) (VOr _ [c,_])) = return c
getCncl _                                      = Nothing

-- | reduces true implication having no conclusion to the relevant
--   of its false premisis.
rdcFalsePrms :: V -> Maybe V
rdcFalsePrms (VImpl (HNFValue Valid) (VOr _ [VNot (HNFValue Valid) p])) = rdcFalse p
rdcFalsePrms _                                                          = Nothing

-- | reduces false values having denied premisis
rdcDndPrmsFalse :: V -> Maybe V
rdcDndPrmsFalse v | not $ isFalseT $ valT v = Nothing
rdcDndPrmsFalse v = case v of
  VCatch t e v'       -> rdcDndPrmsFalse v' >>= return . VCatch t e
  VNot t v'           -> rdcDndPrms v' >>= return . VNot t
  VAnd t (v':_)       -> rdcDndPrmsFalse v' >>= return . VAnd t . return
  VOr t vs            -> (sequence $ map rdcDndPrmsFalse vs) >>= return . VOr t
  VDefEqvl l t v'     -> rdcDndPrmsFalse v' >>= return . VDefEqvl l t
  VForall t v'        -> rdcDndPrmsFalse v' >>= return . VForall t
  VExist _ (VOr _ []) -> return v
  VExist t v'         -> rdcDndPrmsFalse v' >>= return . VExist t
  _                   -> Nothing

-- | reduces ture values - having implications with no conclusions, i.e. denied premises
--   - to its relevant part.
rdcDndPrms :: V -> Maybe V
rdcDndPrms v | not $ isTrueT $ valT v = Nothing
rdcDndPrms v = case v of
  VImpl _ _             -> case getCncl v of
                             Nothing -> rdcFalsePrms v
                             Just _  -> Nothing
  VCatch t e v'         -> rdcDndPrms v' >>= return . VCatch t e
  VNot t v'             -> rdcDndPrmsFalse v' >>= return . VNot t 
  VAnd t vs             -> (exstJust $ map rdcDndPrms vs) >>= return . VAnd t
  VOr t vs              -> (exstJust $ map rdcDndPrms vs) >>= return . VOr t
  -- VEqvl t v'         -> are considered not having denied premises
  VDefEqvl l t v'       -> rdcDndPrms v' >>= return . VDefEqvl l t
  VForall _ (VAnd _ []) -> return v  -- XEmpty or wide = 0!
  VForall t v'          -> rdcDndPrms v' >>= return . VForall t
  VExist t v'           -> rdcDndPrms v' >>= return . VExist t
  _                     -> Nothing
  
--------------------------------------------------------------------------------
-- rdcFailed -

-- | reduces failed values to its relevant part.
rdcFailed :: V -> Maybe V
rdcFailed v = case v of
  VFailure _                  -> return v
  VCheck (Failure _) _        -> return v
  VCatch (Failure _) _ _      -> return v
  VNot f@(Failure _) v'       -> rdcFailed v' >>= return . VNot f
  VAnd f@(Failure _) (v':_)   -> rdcFailed v' >>= return . VAnd f . return
  VAnd (Failure _) []         -> return v
  VOr f@(Failure _) (v':_)    -> rdcFailed v' >>= return . VOr f . return
  VOr (Failure _) []          -> return v
  VImpl f@(Failure _) v'      -> rdcFailed v' >>= return . VImpl f
  VEqvl f@(Failure _) v'      -> rdcFailed v' >>= return . VEqvl f
  VDefEqvl l f@(Failure _) v' -> rdcFailed v' >>= return . VDefEqvl l f
  VForall f@(Failure _) v'    -> rdcFailed v' >>= return . VForall f
  VExist f@(Failure _) v'     -> rdcFailed v' >>= return . VExist f
  _                           -> Nothing

--------------------------------------------------------------------------------
-- relevantLabel -

-- | defines the relevant labels to be /counted/ by 'tests'.
relevantLabel :: Label -> Bool
relevantLabel l = case l of
                    Prms -> False
                    Cncl -> False
                    _    -> True 

--------------------------------------------------------------------------------
-- tests -

-- | path of strings.
type SPath = [String]

-- | the list of all relevant tests - i.e @'VDedEqvl l _@ where @l = 'Label' _@
--   - together with the number of tests.
tests :: V -> [(Int,SPath)]
tests v = case v of
  VDefEqvl l _ v' | relevantLabel l -> map (\(n,p) -> (n,show l:p)) $ tests v'
                  | otherwise       -> tests v'
  VCatch _ _ v'   -> t1 : tests v'
  VNot _ v'       -> t1 : tests v'
  VAnd _ vs       -> t1 : (join $ map tests $ vs)
  VOr _ vs        -> t1 : (join $ map tests $ vs)
  VImpl _ v'      -> t1 : tests v'
  VEqvl _ v'      -> t1 : tests v'
  VForall _ v'    -> t1 : tests v'
  VExist _ v'     -> t1 : tests v'
  _               -> [t1]
  where t1 = (1,[])

----------------------------------------
-- cntTests -

-- | number of 'tests'.
cntTests :: V -> Int
cntTests v = case v of
  VDefEqvl _ _ v' -> cntTests v'
  VAnd _ vs       -> 1+foldl (+) 0 (map cntTests vs)
  VOr _ vs        -> 1+foldl (+) 0 (map cntTests vs)
  VCatch _ _ v'   -> 1+cntTests v'
  VNot _ v'       -> 1+cntTests v'
  VImpl _ v'      -> 1+cntTests v'
  VEqvl _ v'      -> 1+cntTests v'
  VForall _ v'    -> 1+cntTests v'
  VExist _ v'     -> 1+cntTests v'
  _               -> 1


-- | number of 'tests' for true values. __Note__ Before counting the tests they
--   will be first reduced to there relevant part (see 'rdcTrue').
cntTestsRdcTrue :: V -> Int
cntTestsRdcTrue = fromMaybe 0 . fmap cntTests . rdcTrue
  -- sum . map fst . fromMaybe [] . fmap tests . rdcTrue

-- | number of 'tests' for false values. __Note__ Before counting the tests they
--   will be first reduced to there relevant part (see 'rdcFalse').
cntTestsRdcFalse :: V -> Int
cntTestsRdcFalse = fromMaybe 0 . fmap cntTests . rdcFalse
  -- sum . map fst . fromMaybe [] . fmap tests . rdcFalse

-- | number of 'tests' for values containing denied premises. __Note__ Before counting
--   the tests they will be first reduced to there relevant part (see 'rdcDndPrms').
cntTestsRdcDndPrms :: V -> Int
cntTestsRdcDndPrms = fromMaybe 0 . fmap cntTests . rdcDndPrms
  -- sum . map fst . fromMaybe [] . fmap tests . rdcDndPrms

-- | number of 'tests' for failed values. __Note__ Before counting the tests they
--   will be first reduced to there relevant part (see 'rdcFailed').
cntTestsRdcFailed :: V -> Int
cntTestsRdcFailed = fromMaybe 0 . fmap cntTests . rdcFailed

--------------------------------------------------------------------------------
-- xValue' -

-- | @xWO l h@ is the random variable over wide and omgea, where the wide is bounded between @l@ and
-- @h@. 
xWO :: Wide -> Wide -> X (Wide,Omega) 
xWO l h = xTupple2 (xIntB l h) xOmega

-- | random variable of valuation values according to the randomly given 'Wide' and 'Omega'.
xValue :: Statement -> X (Wide,Omega) -> X (IO V)
xValue p = fmap $ uncurry $ value p

-- | pretty showing the value of a statement according to the given 'Wide' and randomly given 'Omega'. 
showVStatement :: Wide -> Statement -> IO ()
showVStatement w s = do
  o <- getOmega
  v <- value s w o
  putStr $ showV (indent0 "  ") v

  



