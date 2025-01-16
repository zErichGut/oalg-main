
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      : OAlg.Control.Validate
-- Description : a tool kit for automatic testing
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
-- 
-- Validation of 'Statement's, based on a stochastic approach.
-- 
-- __Example__ Deterministic statements
-- 
-- >>> validate (SValid && (SInvalid || SValid))
-- Valid
-- 
-- The validation shows the following output:
-- 
-- @
-- >> Omega (StdGen {unStdGen = SMGen 1872899651221430933 9051984386581193015})
-- >> --------------------------------------------------------------------------------
-- >> Summary
-- >> 1 sample tested where 0 tests are false, having 0 denied premises
-- >> 5 tests with a false ratio of 0% and a denied premises ratio of 0%
-- @
-- 
-- From the third line on the number of samples is shown and how many tests over all have been
-- performed to determine the result.
-- As the above statement is obviously deterministic, only one sample has been tested, as the result
-- is independent of the used stochastic.
-- 
--  __Example__ Non deterministic statements
-- 
-- >>> validate (Forall (xIntB 0 100) (\i -> (i <= 100) :?> Params["i":=show i]))
-- ProbablyValid
-- 
-- The validation shows the following output:
-- 
-- @
-- >> Omega (StdGen {unStdGen = SMGen 8429292192981378265 11527977991108410805})
-- >> --------------------------------------------------------------------------------
-- >> Summary
-- >> 10 samples tested where 0 tests are false, having 0 denied premises
-- >> 94 tests with a false ratio of 0% and a denied premises ratio of 
-- @
-- 
-- As this statement is non deterministic, the validation of it pics randomly 10 samples of
-- 'Omega's and 'Wide's (see the number of samples in the summery above) - starting from the shown
-- 'Omega' - and uses 'validateStoch' to determine for each sample the result. All this results are
-- combined with the '&&'-operator to yield the final result.
-- 
-- __Example__ Lazy validation
-- 
-- >>> validate (SValid || throw DivideByZero)
-- Valid
-- 
-- __Example__ Denied premises
--
-- >>> let s = Forall xInt (\i -> (i == i+1):?>Params["i":=show i]) in validate (s :=> s)
-- Valid
-- 
-- The validation shows the following output:
-- 
-- @
-- >> Omega (StdGen {unStdGen = SMGen 1872899651221430933 9051984386581193015})
-- >> --------------------------------------------------------------------------------
-- >> Summary
-- >> 1 sample tested where 0 tests are false, having 4 denied premises
-- >> 7 tests with a false ratio of 0% and a denied premises ratio of 57%
-- @
-- 
-- The statement @s@ is obviously invalid but the tautology @s ':=>' s@ is valid because of denied
-- premises, which is shown in the summery.
-- 
-- __Example__ Invalid statements
-- 
-- >>> validate (Forall (xIntB 0 10) (\i -> (10 < i):?>Params["i":=show i]))
-- Invalid
-- 
-- The validation shows the following output:
-- 
-- @
-- >> Omega (StdGen {unStdGen = SMGen 8429292192981378265 11527977991108410805})
-- >> --------------------------------------------------------------------------------
-- for all Invalid
--   and Invalid
--     check Invalid
--       Invalid
--       parameters
--         i := 9
-- 
-- >> --------------------------------------------------------------------------------
-- >> Summary
-- >> 1 sample tested where 3 tests are false, having 0 denied premises
-- >> 3 tests with a false ratio of 100% and a denied premises ratio of 0%
-- @
-- 
-- where from the third line on the invalid test is shown and the summery shows that in the first
-- sample for 'Omega' and 'Wide' an invalid test has been found.
-- 
--  __Example__ Tracking of exceptions
-- 
-- >>> validate (SValid && (Label "bad" :<=>: throw DivideByZero))
-- *** Exception: FailedStatement divide by zero
-- 
-- The validation shows the following output:
-- 
-- @
-- >> Omega (StdGen {unStdGen = SMGen 3069986384088197145 15225250911862971905})
-- >> --------------------------------------------------------------------------------
-- >> failed sample
-- and divide by zero
--   (bad) divide by zero
--     failure divide by zero
-- 
-- >> --------------------------------------------------------------------------------
-- >> Summary
-- >> 1 sample tested where 0 tests are false, having 0 denied premises
-- >> 3 tests
-- @
-- 
-- The failed sample part of the output shows that in an /and/ construct the component - labeled by
-- @bad@ - has been throwing an exception during the validation process.
-- 
-- __Example__ Extended stochastic
-- 
-- If we validate the obviously false statement
-- 
-- >> validate Forall (xIntB 0 1000) (\i -> (i < 1000) :?> Params["i":=show i])
-- 
-- the validation may nevertheless yield 'ProbablyValid' - because all randomly picked 'Omega's
-- and 'Wide's may produce only values which are strict smaller then @1000@. To overcome this
-- /problem/ and to get more confidence of the result it is possible to adapt the stochastic and use
-- @'validateStochastic' 'Massive'@ instead ('validate' is equivalent to
-- @'validateStochastic' 'Sparse'@).
-- 
-- __Note__ The here defined validation is highly inspired by the QuickCheck package. But we have
-- chosen to adopt the idea to fit more our needs. For example, if a statement throws an exception,
-- then the occurrence can be tracked. Also we devoted special attention to the logic of statements
-- (as 'Statement' is an instance 'Boolean', they fulfill all the logical tautologies). For example,
-- the simple tautology @s ':=>' s@ breaks, if you don't take special care during the validating
-- process or if you allow user interactions.
module OAlg.Control.Validate
  (
    validate, validate'

  , validateStochastic, Stochastic(..)
  , validateStatistics
  , validateWith, Cnfg(..), Result(..), stdCnf, stdStc

  )
  where

import Prelude(Enum(..),Bounded,seq,Int,Integer,Double,Num(..),Fractional(..))
import Control.Monad
import Control.Exception
import System.IO (IO,hFlush,stdout,putStrLn)

import Data.Time
import Data.Time.Clock.System
import Data.Time.Clock.TAI

import Data.List (take,dropWhile,(++),reverse,map)

import OAlg.Category.Definition
import OAlg.Control.Verbose
import OAlg.Control.HNFData

import OAlg.Data.Logical
import OAlg.Data.Ord
import OAlg.Data.Statement

import OAlg.Data.Boolean
import OAlg.Data.Equal
import OAlg.Data.X
import OAlg.Data.Maybe
import OAlg.Data.Show
import OAlg.Data.Statistics

data ValidateException
  = FailedStatement SomeException
  deriving Show

instance Exception ValidateException

--------------------------------------------------------------------------------
-- Stochastic -

-- | defines the stochastic behavior of 'validateStochastic'.
data Stochastic
  = Sparse 
  | Standard
  | Massive
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

--------------------------------------------------------------------------------
-- validate'

-- | short cut for 'validateDet' and should be used mainly in interactiv mode.
validate' :: Statement -> Bool
validate' s = validateDet s

--------------------------------------------------------------------------------
-- Cnfg -

-- | configuration of validating.
data Cnfg
  = Cnfg
  { -- | initial state.
    cnfOmega            :: Maybe Omega

    -- | number of samples to be validated. 
  , cnfSamples          :: Int

    -- | range of wide.
  , cnfWide             :: (Int,Int)

    -- | maximal time for validateing in seconds.
  , cnfMaxDuration      :: Int

    -- | duration between two log entires in seconds.
  , cnfLogDuration      :: Int

    -- | 'True' with statistics.
  , cnfStatistics       :: Bool

    -- | number of labels to be shown for the statistics over all.
  , cnfStcPathLength    :: Int

  } deriving Show

--------------------------------------------------------------------------------
-- stdCnf -

-- | standard configuration
stdCnf :: Cnfg
stdCnf = Cnfg { cnfOmega         = Nothing
              , cnfSamples       = 100
              , cnfWide          = (5,10)
              , cnfMaxDuration   = 5
              , cnfLogDuration   = 20
              , cnfStatistics    = False
              , cnfStcPathLength = 3
              }

--------------------------------------------------------------------------------
-- Result -

-- | result of the validation.
data Result
  = Result
  { rsValid            :: Maybe Valid
  , rsValidatedSamples :: Int
    -- | number of tests over all
  , rsTests      :: Int

    -- | number of false tests from a non valid sample
  , rsTestsFalse   :: Int

    -- | number of tests from reduced denied premises
  , rsTestsRdcDndPrms    :: Int
  }
  deriving (Show)

--------------------------------------------------------------------------------
-- validateWith -

-- | validates the proposition with the given configuration and stochastic.
validateWith :: Cnfg -> Statement -> IO Valid
validateWith cnf s = do
  tStart <- getSystemTime
  o      <- case cnfOmega cnf of
              Nothing -> getOmega
              Just o  -> return o
  putMessage $ show $ o
  (res,mvs) <- let (wl,wh) = cnfWide cnf
                   sts     = cnfStatistics cnf
                   ivs     = take (cnfSamples cnf) $ samples (xValue s (xWO wl wh)) o
                in doValidation cnf tStart sts ivs
  case mvs of
    Just vs -> putStatisticV cnf vs
    _       -> return ()
  putSummary res
  return $ fromJust $ rsValid res

----------------------------------------
-- doValidation -

type Pico = Integer

toPico :: Int -> Pico
toPico d = toEnum d * 1000000000000 -- = 1e12

tDiff :: SystemTime -> SystemTime -> Pico
tDiff s e = diffTimeToPicoseconds $ diffAbsoluteTime (t e) (t s)
  where t = systemToTAITime

doValidation :: Cnfg -> SystemTime -> Bool -> [IO V] -> IO (Result,Maybe [V])
doValidation cnf tStart sts ivs = do
  dvld tStart ivs res (if sts then Just [] else Nothing)
  where res = Result
              { rsValid             = Just Valid
              , rsValidatedSamples  = 0
              , rsTests             = 0
              , rsTestsFalse        = 0
              , rsTestsRdcDndPrms   = 0
              }

        Valid &&> _ = Valid
        a     &&> b = a && b

        halt res = case rsValid res of
          Nothing -> True
          Just b  -> b /= ProbablyValid
          
        putLog res tLast t
          | drtn      = do
              putRsSamples res
              hFlush stdout
              getSystemTime
          | otherwise = return tLast
          where drtn = tDiff tLast t > (toPico $ cnfLogDuration cnf)

        more res ivs tStart t
          | halt res            = return []
          | drtn                = return []
          | otherwise           = return ivs
          where drtn = tDiff tStart t > (toPico $ cnfMaxDuration cnf)

        dvld _ [] res mvs           = return (res,mvs)
        dvld tLast (iv:ivs) res mvs = mvs `seq` do
          v      <- iv
          res'   <- dres (valT v) v res
          tLast' <- getSystemTime >>= putLog res tLast
          ivs'   <- getSystemTime >>= more res' ivs tStart
          dvld tLast' ivs' res' (mvs >>= return . (v:)) 

        dres (HNFValue sb) v res | sb < ProbablyValid = do
          putFalse v
          return res{ rsValid            = fmap (sb&&>) $ rsValid res 
                    , rsValidatedSamples = rsValidatedSamples res + 1
                    , rsTests            = rsTests res + cntTests v
                    , rsTestsFalse       = rsTestsFalse res + cntTestsRdcFalse v
                    }
          
        dres (HNFValue sb) v res = do
          return res{ rsValid            = fmap (sb&&>) $ rsValid res
                    , rsValidatedSamples = rsValidatedSamples res + 1
                    , rsTests            = rsTests res + cntTests v
                    , rsTestsRdcDndPrms  = rsTestsRdcDndPrms res + cntTestsRdcDndPrms v
                    }
          
        dres (Failure e) v res = do
          res' <- return res{ rsValid            = Nothing
                            , rsValidatedSamples = rsValidatedSamples res + 1
                            , rsTests            = rsTests res + cntTests v
                            }
          putFailed v
          putSummary res'
          throw $ FailedStatement $ toException e

----------------------------------------
-- putMessage -
putMessage :: String -> IO ()
putMessage msg = putStrLn (">> " ++ msg)

----------------------------------------
-- putFalse -

putFalse :: V -> IO ()
putFalse v = do
  putMessage "--------------------------------------------------------------------------------"
  putValue (rdcFalse v)

----------------------------------------
-- putFailed -
putFailed :: V -> IO ()
putFailed v = do
  putMessage "--------------------------------------------------------------------------------"
  putMessage "failed sample"
  putValue (rdcFailed v)
  
----------------------------------------
-- putValue -

putValue :: Maybe V -> IO ()
putValue Nothing  = return ()
putValue (Just v) = putStrLn $ showV (indent0 "  ") v

----------------------------------------
-- putStatisticV -
putStatisticV :: Cnfg -> [V] -> IO ()
putStatisticV cnf vs = do
  -- putMessage "statistics of false "
  putMessage "statistics over all"
  putStatisticW [] $ tsts (Just $ cnfStcPathLength cnf) vs
  putMessage "statistics of false"
  putStatisticW [] $ tsts Nothing $ catMaybes $ map rdcFalse vs
  putMessage "statistics of denied premises"
  putStatisticW [] $ tsts Nothing $ catMaybes $ map rdcDndPrms vs
  where tsts mn = map (\(n,p) -> (n,reverse $ mtake p)) . join . map tests
          where mtake = case mn of
                          Just n -> take n
                          _      -> id

----------------------------------------
-- putSummary -
putSummary :: Result -> IO ()
putSummary r = do
  putMessage "--------------------------------------------------------------------------------"
  putMessage "Summary"
  putRsSamples r
  putRsTests (rsValid r) r


nshow :: Int -> String -> String
nshow n s = jtween " " [show n,s'] where s' = s ++ if n == 1 then "" else "s"

putRsSamples :: Result -> IO ()
putRsSamples r = do
  putMessage $ jtween " " [ nshow (rsValidatedSamples r) "sample"
                          , "tested where"
                          , nshow (rsTestsFalse r) "test"
                          , "are false, having"
                          , show (rsTestsRdcDndPrms r)
                          , "denied premises"
                          ]

putRsTests :: Maybe Valid -> Result -> IO ()
putRsTests (Just _) r = do
  putMessage $ jtween " " [ nshow (rsTests r) "test"
                          , "with a false ratio of"
                          , pshow (rsTestsFalse r) (rsTests r)
                          , "and a denied premises ratio of"
                          , pshow (rsTestsRdcDndPrms r) (rsTests r) 
                          ]
  where pshow a b = dropWhile (== ' ') $ vshow Low $ Percent (a' / b')
          where a' = toEnum a :: Double
                b' = toEnum b

putRsTests Nothing r = putMessage $ nshow (rsTests r) "test"
        
--------------------------------------------------------------------------------
-- test -

-- | adapts the standard configuration 'stdCnf' according to the given stochastic.
stdStc :: Stochastic -> Cnfg
stdStc s = case s of
  Sparse   -> stdCnf{ cnfSamples     = 10
                    , cnfMaxDuration = 2
                    }
  Standard -> stdCnf
  Massive  -> stdCnf{ cnfSamples     = 10000
                    , cnfMaxDuration = 300
                    }

--------------------------------------------------------------------------------
-- validateStochastic -

-- | validates the statement with the configuration given by 'stdStc',
validateStochastic :: Stochastic -> Statement -> IO Valid
validateStochastic = validateWith . stdStc 

--------------------------------------------------------------------------------
-- validate -

-- | validates a statement.
validate :: Statement -> IO Valid
validate = validateWith cnf{cnfStatistics = False} where cnf = stdStc Sparse

--------------------------------------------------------------------------------
-- validateStatistics -

-- | validates a statement according to the given stochastic with showing the statistics.
validateStatistics :: Stochastic -> Statement -> IO Valid
validateStatistics c s = validateWith cnf{cnfStatistics = True} s where cnf = stdStc c

