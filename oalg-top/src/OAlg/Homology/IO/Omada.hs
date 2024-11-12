
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
-- Module      : OAlg.Homology.IO.Omada
-- Description : read-eval-print cycle for omada
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- read-eval-print cycle for exploring the homology of a complex.
module OAlg.Homology.IO.Omada
  () where

import Control.Exception

import System.IO

import OAlg.Control.Validate

import OAlg.Data.Number
import OAlg.Data.Symbol (Symbol())
import OAlg.Data.Validable
import qualified OAlg.Data.Statement.Definition as S

import OAlg.Entity.Definition (Entity())
import OAlg.Entity.Natural (Attestable(..), SomeNatural(..), someNatural, N0)
import OAlg.Entity.Sequence.Set

import OAlg.Homology.ChainComplex
import OAlg.Homology.Complex

import OAlg.Homology.IO.Evaluation
import OAlg.Homology.IO.Parser.Definition (ParserFailure(..),LexerFailure(..),Pos, Token(..))
import OAlg.Homology.IO.Parser.Instruction
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
            , ("C",valGenerator hs (ChainGenerator ChainGenerator'))             
            , ("D",valGenerator hs (ChainGenerator CycleGenerator))             
            , ("L",valGenerator hs (ChainGenerator HomologyGroupGenerator'))
            , ("H",valHomologyGroups hs)
            , ("K",valGenerator hs HomologyGroupGenerator)
            , ("#",OperatorValue SpanOperator)
            , ("d",OperatorValue BoundaryOperator)
            , ("b",OperatorValue Boundary'Operator)
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
  Plane a b        -> return $ initSomeEnv r (complex $ plane (s a) (s b)) where
    s :: N -> Set N
    s 0 = Set []
    s n = Set [0..pred n]
    
--------------------------------------------------------------------------------
-- seEmpty -

seEmpty :: IO SomeEnv
seEmpty = someEnv Regular EmptyComplex

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
  DuplicateVars w p     -> putFailure hErr (pos m p) (  "duplicate variables '" ++ w ++ "'")
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

putEvalFailure :: Handle -> Mode -> Ln -> EvaluationFailure x -> IO ()
putEvalFailure hErr m l f = case f of
  ValueFailure f' _   -> case f' of
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
rep :: Mode -> Handle -> Handle -> Handle -> SomeEnv -> IO SomeEnv
rep md hIn hOut hErr se = rep' (0::Integer) se where

  putPromt Interactive = do
      hFlush hOut
      hPutStr hOut "omada> "
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

  getTermValue :: Env n x -> Maybe (TermValue x) -> IO (TermValue x)
  getTermValue e mt = return $ case mt of
    Nothing -> envLookup e "it"
    Just t  -> t

  putValidationResult :: Handle -> S.Valid -> IO ()
  putValidationResult hOut v = hPutStrLn hOut ("Result: " ++ show v)

  rep' l se = do
    putPromt md
    eof <- hIsEOF hIn
    case eof of
      True  -> quit >> return se
      False -> hGetLine hIn >>= ep' (l+1) se

  ep' l se@(SomeEnv e) ln = case prsInstruction ln of
    Right exp          -> case exp of
      Empty            -> rep' l se
      Command cmd      -> case cmd of
        Quit           -> quit >> return se
        Help           -> putHelp >> rep' l se
        SetComplex r c -> do
                          se' <- someEnv r c `catch` loadException se
                          rep' l se'
        Let x t        -> case evalValue e t of
          Right v      -> rep' l (SomeEnv $ envAlter e x v)
          Left f       -> putEvalFailure hErr md l f >> rep' l se
        Valid mt       -> do
                          t <- getTermValue e mt
                          case evalValue e t of
                            Right v -> validate (valid v) >>= putValidationResult hOut
                            Left f  -> putEvalFailure hErr md l f
                          rep' l se
      TermValue t      -> case evalValue e t of
        Right v        -> putResult v >> rep' l (SomeEnv $ envAlter e "it" v)
        Left f         -> putEvalFailure hErr md l f >> rep' l se
    Left f             -> putParserFailure hErr md f >> rep' l se


someExcp :: Handle -> SomeEnv -> SomeException -> IO SomeEnv
someExcp hErr se e = (hPutStrLn hErr $ show e) >> return se

repi :: IO ()
repi = seEmpty >>= rep Interactive stdin stdout stderr >> return ()

repb' :: FilePath -> Handle -> Handle -> SomeEnv -> IO SomeEnv
repb' f hOut hErr se = do
  hIn <- openFile f WriteMode
  se' <- rep Batch hIn hOut hErr se `catch` someExcp hErr se
  hClose hIn
  return se'

repb :: FilePath -> IO ()
repb f = seEmpty >>= repb' f stdout stderr >> return ()


