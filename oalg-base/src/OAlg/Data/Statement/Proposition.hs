
{-# LANGUAGE NoImplicitPrelude #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs, StandaloneDeriving, ExistentialQuantification, RankNTypes #-}


-- |
-- Module      : OAlg.Data.Statement.Proposition
-- Description : proposition on statements
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- Propositions on statements.
module OAlg.Data.Statement.Proposition
  (
    -- * Proposition
    prpStatement
  , prpStatementTautologies
  , prpValidTautologies

  , prpCheckTrue, prpCheckFalse
  , prpCatch
  , prpPrjHom

    -- * X
  , xStatement
  
  )
  where

import System.IO (IO)

import Control.Monad
import Control.Applicative ((<*>))

import Data.List (map,(++),take,repeat)

import OAlg.Control.Exception
import OAlg.Category.Definition

import OAlg.Data.Ord
import OAlg.Data.Show
import OAlg.Data.Equal
import OAlg.Data.Statistics
import OAlg.Data.Canonical
import OAlg.Data.Number
import OAlg.Data.X

import OAlg.Data.Boolean
import OAlg.Data.Statement.Definition



--------------------------------------------------------------------------------
-- xPoroposition -

xPrpOp :: X (Statement -> Statement -> Statement)
xPrpOp = xOneOf [(:||),(:&&),(:=>),(:<=>)]

xPrpOps ::X ([Statement] -> Statement)
xPrpOps = xOneOf [And,Or]

xStatement' :: Int -> X Statement -> X (X x,x -> Statement) -> X Statement
xStatement' n xp0 xxp = xprp n
  where -- xprp :: Int -> X Statement
        xprp 0 = xp0        
        xprp n = join $ xOneOfW [ (10,xOp)
                                , (4,xOps)
                                , (3,xNot)
                                , (2,xForall xxp)
                                , (2,xExist xxp)
                                , (1,xCatch)
                                , (1,xCheck)
                                , (1,xEqvDef)
                                ]
          where n' = pred n

                xCheck = do
                  b <- xOneOf [False,True]
                  return (b :?> Message "m")

                xCatch = do
                  e <- xOneOf [AlgebraicException "",ImplementationError ""]
                  return (throw e `Catch` algExcp)
                  where algExcp (AlgebraicException _) = SValid
                        algExcp _                      = SInvalid

                xNot = do
                  i <- xIntB 0 n'
                  p <- xprp i
                  return (Not p)

                -- xOp :: X Statement
                xOp = do
                  i  <- xIntB 0 n'
                  j  <- xIntB 0 n'
                  xPrpOp <*> xprp i <*> xprp j

                -- xOps :: X Statement
                xOps = do
                  l   <- xIntB 0 10
                  ps  <- xList $ map (join . fmap xprp)
                                     $ (take l) $ repeat $ xIntB 0 n'
                  ops <- xPrpOps
                  return (ops ps)

                -- xEqvDef :: X Statement
                xEqvDef = do
                  i <- xIntB 0 n'
                  p <- xprp i
                  return (Label "s" :<=>: p)

                -- xForall :: X Statement
                xForall xxp = do
                  (x,p) <- xxp
                  return (Forall x p)

                xExist xxp = do
                  (x,p) <- xxp
                  return (Exist x p)

--------------------------------------------------------------------------------
-- xStatement -

-- | random variable of statements with the maximal given depth.  
xStatement :: Int -> X Statement
xStatement n = xStatement' n xp0 xxp
  where xp0 = xOneOf [SValid,SInvalid]
        xxp = xOneOf ([ (xIntB 0 100, \n -> (n `modInt` 2 == 0) :?> Message (show n))
                      , (xIntB 0 100, \n -> (90 <= n) :?> Message (show n))
                      , (xIntB 0 100, \n -> (n <= 10) :?> Message (show n))
                      , (xInt       , const SValid)
                      , (xInt       , const SInvalid)
                      ]
                      ++ if 0 < n'
                           then [(xInt,\n -> sample (xStatement n') (mkOmega n))]
                           else []
                     )
                     
        n' = n `divInt` 3
            
dstXStatement :: Wide -> Int -> Int -> IO ()
dstXStatement w n m = do
  o  <- getOmega
  o' <- return $ sample xOmega o 
  ps <- return $ take m $ samples (xStatement n) o
  vs <- sequence $ map (\p -> value p w o') ps
  putStatistic [id] $ map (show . valT) vs


--------------------------------------------------------------------------------
-- prpStatementTautologies -

-- | logical tautologies of 'Statement'.
--
--  __Note__ Validating this proposition produces about 15% denied premises, which is OK.
prpStatementTautologies :: Statement
prpStatementTautologies = Prp "StatementTautologies" 
    :<=>: prpTautologies id xPrp (xTakeB 0 11 xPrp)
  where
    xPrp = xStatement 7
    
--------------------------------------------------------------------------------
-- prpValidTautologies -

-- | logical tautologies of 'Valid'.
prpValidTautologies :: Statement
prpValidTautologies = Prp "ValidTautologies"
  :<=>: prpTautologies stm xValid (xTakeB 0 20 xValid)
  where stm Invalid         = SInvalid
        stm ProbablyInvalid = Exist xInt (const SInvalid)
        stm ProbablyValid   = Forall xInt (const SValid)
        stm Valid           = SValid

--------------------------------------------------------------------------------
-- prpCatch -

-- | catch algebraic exceptions.
prpCatch :: Statement
prpCatch = Prp "Catch"
  :<=>: And [ (throw (AlgebraicException "") `Catch` algException) <~> true
            , (throw (ImplementationError "") `Catch` algException) <~> false
            ]
            
  where algException :: AlgebraicException -> Statement
        algException (AlgebraicException _) = SValid
        algException _                      = SInvalid

--------------------------------------------------------------------------------
-- prpCheckFalse -

-- | @'false' ':?>' 'MInvalid' '<~>' 'false'@.
prpCheckFalse :: Statement
prpCheckFalse = Prp "CheckFalse" :<=>: false :?> Message "" <~> false

--------------------------------------------------------------------------------
-- prpCheckTrue -

-- | @'true' ':?>' 'MInvalid'@.
prpCheckTrue :: Statement
prpCheckTrue = Prp "CheckTrue" :<=>: True :?> Message ""

--------------------------------------------------------------------------------
-- prpPrjHom -

-- | @'prj' :: 'Valid' -> 'Bool'@ is a homomorphism between 'Boolean' structures.
prpPrjHom :: Statement
prpPrjHom = Prp "PrjHom" :<=>: Label "Valid -> Bool"
  :<=>: And [ h true .==. true
            , h false .==. false
            , Forall xa  (\a -> h (not a) .==. not (h a))
            , Forall xab (\(a,b) -> h (a && b) .==. (h a && h b))
            , Forall xab (\(a,b) -> h (a || b) .==. (h a || h b))
            , Forall xab (\(a,b) -> h (a ~> b) .==. (h a ~> h b))
            ]
  where h   = prj :: Valid -> Bool
        xa  = xValid
        xab = xTupple2 xa xa
        
--------------------------------------------------------------------------------
-- prpStatement -

-- | validity of the logic of 'Statement'..
prpStatement :: Statement
prpStatement = Prp "Statement"
  :<=>: And [ prpStatementTautologies
            , prpLazy id
            , prpCheckTrue
            , prpCheckFalse
            , prpCatch
            , prpPrjHom
            ]
