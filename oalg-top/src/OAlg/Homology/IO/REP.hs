
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
-- Module      : OAlg.Homology.IO.REP
-- Description : read-eval-print cycle
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- read-eval-print cycle for exploring the homology of a complex.
module OAlg.Homology.IO.REP
  () where

import Control.Exception

import System.IO

import OAlg.Data.Number
import OAlg.Data.Symbol (Symbol())

import OAlg.Entity.Definition (Entity())
import OAlg.Entity.Natural (Attestable(..), SomeNatural(..), someNatural, N0)

import OAlg.Homology.ChainComplex
import OAlg.Homology.Complex

import OAlg.Homology.IO.Term (Term(..))
import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Parser.Definition (ParserFailure(..),LexerFailure(..),Pos, Token(..))
import OAlg.Homology.IO.Parser.Expression
import OAlg.Homology.IO.Help
import OAlg.Homology.IO.Value
import OAlg.Homology.IO.Pretty

--------------------------------------------------------------------------------
-- SomeEnv -

data SomeEnv where
  SomeEnv :: (Entity x, Ord x, Attestable n, Pretty x) => Env n x -> SomeEnv

--------------------------------------------------------------------------------
-- initSomeEnv -

initSomeEnv :: (Entity x, Ord x, Attestable n, Pretty x) => Regular -> Complex n x -> SomeEnv
initSomeEnv r c = SomeEnv $ foldl (<+) e0
            [ ("it", ZValue 0)
            , ("A",valGenerator hs (ChainGenerator ChainGenerator'))             
            , ("B",valGenerator hs (ChainGenerator CycleGenerator))             
            , ("C",valGenerator hs (ChainGenerator HomologyGroupGenerator'))
            , ("H",valHomologyGroups hs)
            , ("K",valGenerator hs HomologyGroupGenerator)
            , ("#",OperatorValue SpanOperator)
            , ("d",OperatorValue BoundaryOperator)
            , ("d'",OperatorValue Boundary'Operator)
            , ("h",OperatorValue HomologyClassOperator)
            ]
             
  where
    e0 = env r c
    hs = envV' e0

    e <+ (k,v) = envAlter e k v  -- altering the environment dos not affect hs

--------------------------------------------------------------------------------
-- someEnv -

someEnv :: Regular -> ComplexId -> IO SomeEnv
someEnv r c = case c of
  EmptyComplex     -> return $ initSomeEnv r (cpxEmpty :: Complex N0 Symbol)
  KleinBottle      -> return $ initSomeEnv r (complex kleinBottle)
  Sphere n         -> case someNatural n of
    SomeNatural n' -> return $ initSomeEnv r (complex $ sphere n' (0 :: N)) 

--------------------------------------------------------------------------------
-- Mode -

data Mode = Interactive | Batch deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- Ln -

-- | line number for batch mode.
type Ln = Integer

--------------------------------------------------------------------------------
-- putFailure -

putFailure :: Handle -> String -> String -> IO ()
putFailure hErr at msg = hPutStrLn hErr ("!!! Failure" ++ at ++ ": " ++ msg)

pshowToken :: Token -> String
pshowToken t = case t of
  Symbol w -> "symbol '" ++ w ++ "'"
  Key w    -> "keyword '" ++ w ++ "'"
  Id w     -> "identifier '" ++ w ++ "'"

putParserFailure :: Handle -> Mode -> ParserFailure -> IO ()
putParserFailure hErr m f = case f of
  EmptyFailure          -> putFailure hErr "at the end" ""
  UnexpectedToken (t,p) -> putFailure hErr (pos m p) ("unexpected " ++ pshowToken t)
  ExpectedToken e (t,p) -> putFailure hErr (pos m p) (  "expected " ++ pshowToken e
                                                     ++ ", but saw " ++ pshowToken t
                                                     )
  ExpectedIdent (t,p)   -> putFailure hErr (pos m p) (  "expected identifier, but saw "
                                                     ++ pshowToken t
                                                     )
  Expected e (t,p)      -> putFailure hErr (pos m p) (  "expected " ++ e
                                                     ++ ", but saw " ++ pshowToken t
                                                     )
  Unparsed t@(_,p) ts   -> putFailure hErr (pos m p) (  "unparsed "
                                                     ++ take 10 (pshows pshowToken $ map fst (t:ts))
                                                     )
  Unknown msg           -> putFailure hErr "" ("unknown " ++ msg)
  LexerFailure u        -> case u of
    UnexpectedChars chs -> putFailure hErr (pos m p) chs' where
      p    = head $ map snd chs
      chs' = (take 10 $ map fst chs) ++ ".."
      
  where
    pos :: Mode -> Pos -> String
    pos md (l,p)  = " at " ++ case md of
      Interactive -> show p
      Batch       -> show (l,p)

putEvalFailure :: (Entity x, Ord x)
  => Handle -> Mode -> Ln -> EvaluationFailure x -> IO ()
putEvalFailure hErr m l f = case f of
  ValueFailure f' t   -> case f' of
    NotApplicable a b -> putFailure hErr (pos m l) ( "not applicable: " ++ pshow a ++ " on "
                                                   ++ pshow b
                                                   )
    NotACycle'        -> putFailure hErr (pos m l) "not a cycle"
    NonTrivialHomologyClass' h
                      -> putFailure hErr (pos m l) (  "non-trivial homology class: "
                                                   ++ pshow h
                                                   )
    InconsistentRoot a b
                      -> putFailure hErr (pos m l) (  "inconsistent root "
                                                   ++ pshow a ++ " and " ++ pshow b
                                                   )
    NotAddable a      -> putFailure hErr (pos m l) (  "not addable: "
                                                   ++ pshow a
                                                   )

  NotAValue t         -> putFailure hErr (pos m l) (pshow t)
  NotAZValue t        -> putFailure hErr (pos m l) ("Z-value expected, but: " ++ pshow t)
  where
    pos :: Mode -> Ln -> String
    pos md l = case md of
      Interactive -> ""
      Batch       -> " at line " ++ show l
    
--------------------------------------------------------------------------------
-- rep

-- | read-evaluate-print cycle.
rep :: Mode -> Handle -> Handle -> Handle -> IO ()
rep md hIn hOut hErr = someEnv Regular EmptyComplex >>= rep' (0::Integer) where

  putPromt Interactive = do
      hFlush hOut
      hPutStr hOut "top> "
  putPromt Batch = return ()
    
  putHelp :: IO ()
  putHelp = hPutStrLn hOut help

  putResult :: (Entity x, Ord x, Pretty x) => Value x -> IO ()
  putResult v = hPutStrLn hOut $ pshow v

  quit = do
    hFlush hOut
    hFlush hErr

  loadException :: SomeEnv -> SomeException -> IO SomeEnv
  loadException se e = hPutStrLn hErr (show e) >> return se
    

  ep' l se@(SomeEnv e) ln = case prsExpression ln of
    Right exp     -> case exp of
      Empty       -> rep' l se
      Command cmd -> case cmd of
        Quit      -> quit
        Help      -> putHelp >> rep' l se
        Load r c  -> do
                     se' <- someEnv r c `catch` loadException se
                     rep' l se'
        Let x t   -> case evalValue e t of
          Right v -> rep' l (SomeEnv $ envAlter e x v)
          Left f  -> putEvalFailure hErr md l f >> rep' l se
      TermValue t -> case evalValue e t of
        Right v   -> putResult v >> rep' l (SomeEnv $ envAlter e "it" v)
        Left f    -> putEvalFailure hErr md l f >> rep' l se
    Left f        -> putParserFailure hErr md f >> rep' l se
      
  rep' l se = do
    putPromt md
    eof <- hIsEOF hIn
    case eof of
      True  -> quit
      False -> hGetLine hIn >>= ep' (l+1) se

repi = rep Interactive stdin stdout stderr

-- ic r = iComplex stdin stdout stderr r (complex kleinBottle) 
repb = do
  hIn <- openFile "c:/msys64/home/zeric/foo" ReadMode 
  rep Batch hIn stdout stderr `catch` all
  hClose hIn

  where 
    all :: SomeException -> IO ()
    all e = hPutStrLn stderr $ show e
  

