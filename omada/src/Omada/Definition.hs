
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
-- Module      : Omada.Definition
-- Description : read-eval-print loop for omada
-- Copyright   : (c) Erich Gut
-- License     : BSD3
-- Maintainer  : zerich.gut@gmail.com
--
-- read-eval-print loop for exploring the homology groups of a simplical complex. Start for
-- example 'repli' and enter @:help@ to get the help-page.
module Omada.Definition
  ( repl, repli, replb, Mode(..)

  , someEnv, seEmpty, SomeEnv()

    -- Exception
  , OmadaException(..)
  ) where

import Control.Exception

import System.IO

import OAlg.Control.Validate

import OAlg.Data.Number
import OAlg.Data.Symbol (Symbol())
import OAlg.Data.Validable
import qualified OAlg.Data.Statement.Definition as S

import OAlg.Entity.Definition (Entity())
import OAlg.Entity.Natural (Attestable(..), SomeNatural(..), someNatural, N0, W(SW))
import OAlg.Entity.Sequence.Set

import OAlg.Homology.Simplex (simplex)
import OAlg.Homology.ChainComplex
import OAlg.Homology.Complex

import Omada.Parser.Definition (ParserFailure(..),LexerFailure(..),Pos, Token(..))

import Omada.Evaluation
import Omada.Instruction
import Omada.Help
import Omada.Value
import Omada.Pretty

--------------------------------------------------------------------------------
-- OmadaException -

-- | omada exceptions.
data OmadaException = NotYetImplemented

instance Show OmadaException where show NotYetImplemented = "not yet implemented"

instance Exception OmadaException

--------------------------------------------------------------------------------
-- SomeEnv -

-- | some environment.
data SomeEnv where
  SomeEnv :: (Entity x, Ord x, Attestable n, Pretty x) => Env n x -> SomeEnv

--------------------------------------------------------------------------------
-- initSomeEnv -

-- | initial environment given by a complex.
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

-- | initiates an environment by the given complex.
someEnv :: Regular -> ComplexId -> IO SomeEnv
someEnv r c = case c of
  EmptyComplex     -> return $ initSomeEnv r (cpxEmpty :: Complex N0 Symbol)
  KleinBottle      -> return $ initSomeEnv r (complex kleinBottle)
  MoebiusStrip     -> return $ initSomeEnv r (complex moebiusStrip)
  Torus n | n == 2 -> return $ initSomeEnv r (complex torus2)
  ProjectiveSpace n | n == 2
                   -> return $ initSomeEnv r (complex projectivePlane)
  Sphere n         -> case someNatural n of
    SomeNatural n' -> return $ initSomeEnv r (complex $ sphere n' (0 :: N))
  Simplex n        -> case someNatural n of
    SomeNatural n' -> return $ initSomeEnv r (complex $ Set [simplex (SW n') (0 :: N)])
  Plane a b        -> return $ initSomeEnv r (complex $ plane (s a) (s b)) where
    s :: N -> Set N
    s 0 = Set []
    s n = Set [0..pred n]
  _                -> throw NotYetImplemented
    
--------------------------------------------------------------------------------
-- seEmpty -

-- | empty environment,
seEmpty :: IO SomeEnv
seEmpty = someEnv Regular EmptyComplex

--------------------------------------------------------------------------------
-- Mode -

-- | mode for the read-eval-print loop.
data Mode = Interactive | Batch deriving (Show,Eq,Ord,Enum)

--------------------------------------------------------------------------------
-- Ln -

-- | line number for batch mode.
type Ln = Integer

--------------------------------------------------------------------------------
-- putFailure -

-- | puts a failure.
putFailure :: Handle -> String -> String -> IO ()
putFailure hErr at msg = hPutStrLn hErr ("!!! Failure" ++ at ++ ": " ++ msg)

-- | pretty-show a token.
pshowToken :: Token -> String
pshowToken t = case t of
  Symbol w -> "symbol '" ++ w ++ "'"
  Key w    -> "keyword '" ++ w ++ "'"
  Id w     -> "identifier '" ++ w ++ "'"
  Str w    -> "string \"" ++ w ++ "\""

--------------------------------------------------------------------------------
-- putParserFailure -

-- | puts a parser failure.
putParserFailure :: Handle -> Mode -> Ln -> ParserFailure -> IO ()
putParserFailure hErr m l f = case f of
  EmptyFailure          -> putFailure hErr "at the end" ""
  UnexpectedToken (t,p) -> putFailure hErr (pos m l p) ("unexpected " ++ pshowToken t)
  ExpectedToken e (t,p) -> putFailure hErr (pos m l p) (  "expected " ++ pshowToken e
                                                       ++ ", but saw " ++ pshowToken t
                                                       )
  ExpectedIdent (t,p)   -> putFailure hErr (pos m l p) (  "expected identifier, but saw "
                                                       ++ pshowToken t
                                                       )
  ExpectedString (t,p)  -> putFailure hErr (pos m l p) (  "expected string, but saw "
                                                       ++ pshowToken t
                                                       )
  Expected e (t,p)      -> putFailure hErr (pos m l p) (  "expected " ++ e
                                                       ++ ", but saw " ++ pshowToken t
                                                       )
  Unparsed t@(_,p) ts   -> putFailure hErr (pos m l p) (  "unparsed "
                                                       ++ take 10 (pshows pshowToken $ map fst (t:ts))
                                                       )
  DuplicateVars w p     -> putFailure hErr (pos m l p) (  "duplicate variables '" ++ w ++ "'")
  Unknown msg           -> putFailure hErr "" ("unknown " ++ msg)
  LexerFailure u        -> case u of
    UnexpectedChars chs -> putFailure hErr (pos m l p) chs' where
      p    = head $ map snd chs
      chs' = (take 10 $ map fst chs) ++ ".."
    ExpectedChar c p    -> putFailure hErr (pos m l p) ("expected character '" ++ [c] ++ "'")
    UnexpectedChar c p  -> putFailure hErr (pos m l p) ("unexpected character '" ++ [c] ++ "'")
    UnexpectedEnd       -> putFailure hErr "end of input" "unexpected end" 
      
  where
    pos :: Mode -> Ln -> Pos -> String
    pos md l (_,p)  = " at " ++ case md of
      Interactive -> show p
      Batch       -> show (l,p)

--------------------------------------------------------------------------------
-- putEvalFailure -

-- | puts a evaluation failure.
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
-- someExcp -

-- | handler for some exception.
someExcp :: Handle -> x -> SomeException -> IO x
someExcp hErr x e = (hPutStrLn hErr $ show e) >> return x

--------------------------------------------------------------------------------
-- repl

-- | read-evaluate-print loop for @omada@ with a given mode, a input handle, a output handle and a
--   error handle.
repl :: Mode -> Handle -> Handle -> Handle -> SomeEnv -> IO SomeEnv
repl md hIn hOut hErr se = repl' (0::Integer) se where

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

  getTermValue :: Env n x -> Maybe (TermValue x) -> IO (TermValue x)
  getTermValue e mt = return $ case mt of
    Nothing -> envLookup e "it"
    Just t  -> t

  putValidationResult :: Handle -> S.Valid -> IO ()
  putValidationResult hOut v = hPutStrLn hOut ("Result: " ++ show v)

  repl' l se = do
    putPromt md
    hFlush hOut
    eof <- hIsEOF hIn
    case eof of
      True  -> quit >> return se
      False -> hGetLine hIn >>= ep' (l+1) se

  ep' l se@(SomeEnv e) ln = case prsInstruction ln of
    Right exp          -> case exp of
      Empty            -> repl' l se
      Command cmd      -> case cmd of
        Quit           -> quit >> return se
        Help           -> putHelp >> repl' l se
        Load f         -> do
                          se' <- replb' f hOut hErr se `catch` someExcp hErr se
                          repl' l se'
        SetComplex r c -> do
                          se' <- someEnv r c `catch` someExcp hErr se
                          repl' l se'
        Let x t        -> case evalValue e t of
          Right v      -> repl' l (SomeEnv $ envAlter e x v)
          Left f       -> putEvalFailure hErr md l f >> repl' l se
        Valid mt       -> do
                          t <- getTermValue e mt
                          case evalValue e t of
                            Right v -> validate (valid v) >>= putValidationResult hOut
                            Left f  -> putEvalFailure hErr md l f
                          repl' l se
      TermValue t      -> case evalValue e t of
        Right v        -> putResult v >> repl' l (SomeEnv $ envAlter e "it" v)
        Left f         -> putEvalFailure hErr md l f >> repl' l se
    Left f             -> putParserFailure hErr md l f >> repl' l se


--------------------------------------------------------------------------------
-- repli -

-- | interactive read-eval-print loop for @omada@,
repli :: IO ()
repli = seEmpty >>= repl Interactive stdin stdout stderr >> return ()

--------------------------------------------------------------------------------
-- replb -

-- | batch read-eval-print loop for @omada@ on a given file, a output handle and an error handle.
replb' :: FilePath -> Handle -> Handle -> SomeEnv -> IO SomeEnv
replb' f hOut hErr se = do
  hIn <- openFile f ReadMode
  se' <- repl Batch hIn hOut hErr se `catch` someExcp hErr se
  hClose hIn
  return se'

-- | batch read-eval-print loop for @omada@ on a given file for the standard output and error handle. 
replb :: FilePath -> IO ()
replb f = seEmpty >>= replb' f stdout stderr >> return ()


