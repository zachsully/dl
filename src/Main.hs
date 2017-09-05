{-# LANGUAGE BangPatterns #-}
module Main where

import Data.Monoid
import Options.Applicative
import Control.Monad.State
import Control.Monad (when)

-- local
import qualified DualSyn as D
import qualified HsSyn as H
import Lexer
import Parser
import Translation
import Judgement


--------------------------------------------------------------------------------
--                              Cmdline Options                               --
--------------------------------------------------------------------------------

data CompileMode
  = CompileMode
  { cmDebug  :: Bool
  , cmInput  :: FilePath
  , cmOutput :: FilePath }

data EvalMode
  = EvalMode
  { emDebug  :: Bool
  , emInput  :: FilePath }

data TypeMode
  = TypeMode
  { tmDebug  :: Bool
  , tmInput  :: FilePath }

data Mode
  = Compile  CompileMode
  | Evaluate EvalMode
  | TypeOf   TypeMode

inputFp :: Parser FilePath
inputFp = strArgument (metavar "INPUT" <> help "input dual language file")

parseCompile :: Parser CompileMode
parseCompile = CompileMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> inputFp
           <*> strArgument (metavar "OUTPUT" <> help "output Haskell file")

parseEvaluate :: Parser EvalMode
parseEvaluate = EvalMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> inputFp

parseTypeOf :: Parser TypeMode
parseTypeOf = TypeMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> inputFp

selectMode :: Parser Mode
selectMode =
  subparser $
    (command "compile" (info (helper <*> (Compile <$> parseCompile))
                             (progDesc "compile a dual language program to Haskell")))
           <> (command "eval" (info (helper <*> (Evaluate <$> parseEvaluate))
                              (progDesc "evaluate a dual language program")))
           <> (command "type" (info (helper <*> (TypeOf <$> parseTypeOf))
                                    (progDesc "infer the type of a dual language program")))

parseMode :: IO Mode
parseMode = execParser
          $ info (helper <*> selectMode)
          $ fullDesc <> progDesc "dualpp: a small dualized langauge"


--------------------------------------------------------------------------------
--                                   Main                                     --
--------------------------------------------------------------------------------

main :: IO ()
main = do { mode <- parseMode
          ; case mode of
              Compile cm -> runCompile cm
              Evaluate em -> runEvaluate em
              TypeOf tm -> runTypeOf tm
          }

getProgram :: FilePath -> IO D.Program
getProgram fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; return . fst . runState (parseProgram tokens) $ emptyState
     }

runCompile :: CompileMode -> IO ()
runCompile cm =
  do { pgm <- getProgram (cmInput cm)
     ; when (cmDebug cm) $ print pgm
     ; let prog' = H.ppProgram . translateProgram $ pgm
     ; case cmOutput cm of
         "-" -> putStrLn prog'
         fp  -> writeFile fp prog'
     }

runEvaluate :: EvalMode -> IO ()
runEvaluate em =
  do { term <- D.pgmTerm <$> getProgram (emInput em)
     ; when (emDebug em) $ print term
     ; putStr "> "
     ; print . D.evalEmpty $ term }

runTypeOf :: TypeMode -> IO ()
runTypeOf tm =
  do { pgm <- getProgram (tmInput tm)
     ; when (tmDebug tm) $ print pgm
     ; putStrLn . ppTypeScheme . inferTSProgram $ pgm }
