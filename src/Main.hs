{-# LANGUAGE BangPatterns #-}
module Main where

import Data.Monoid
import Options.Applicative
import Control.Monad.State
import Control.Monad (when)

-- local
import qualified DualSyn as D
import qualified HsSyn as H
import qualified MLSyn as ML
import Lexer
import Parser
import Translation
import Judgement
import Utils


--------------------------------------------------------------------------------
--                              Cmdline Options                               --
--------------------------------------------------------------------------------

data FlattenMode
  = FlattenMode { fmInput :: FilePath }

data CompileMode
  = CompileMode
  { cmDebug  :: Bool
  , cmLocal  :: Bool
  , cmML     :: Bool
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
  = Flatten  FlattenMode
  | Compile  CompileMode
  | Evaluate EvalMode
  | TypeOf   TypeMode

inputFp :: Parser FilePath
inputFp = strArgument (metavar "INPUT" <> help "input dual language file")

parseFlatten :: Parser FlattenMode
parseFlatten = FlattenMode <$> inputFp

parseCompile :: Parser CompileMode
parseCompile = CompileMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> switch (  long "local"
                      <> short 'L'
                      <> help "local compile, that is using a naming convention." )
           <*> switch (  long "ocaml"
                      <> help "compile to Ocaml." )
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
selectMode = subparser
  $  (command "flatten" (info (helper <*> (Flatten <$> parseFlatten))
                              (progDesc "run flattening rewrite rules.")))
  <> (command "compile" (info (helper <*> (Compile <$> parseCompile))
                              (progDesc "compile a dual language program to Haskell.")))
  <> (command "eval" (info (helper <*> (Evaluate <$> parseEvaluate))
                           (progDesc "evaluate a dual language program.")))
  <> (command "type" (info (helper <*> (TypeOf <$> parseTypeOf))
                           (progDesc "infer the type of a dual language program.")))

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
              Flatten fm  -> runFlatten fm
              Compile cm  -> runCompile cm
              Evaluate em -> runEvaluate em
              TypeOf tm   -> runTypeOf tm
          }

getProgram :: FilePath -> IO (D.Program D.Term)
getProgram fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; return . fst . runState (parseProgram tokens) $ emptyState
     }

runFlatten :: FlattenMode -> IO ()
runFlatten fm =
  do { pgm <- getProgram (fmInput fm)
     ; pprint pgm
     ; putStrLn "\n->R\n"
     ; pprint . D.flatten . D.pgmTerm $ pgm
     }

runCompile :: CompileMode -> IO ()
runCompile cm =
  do { pgm <- getProgram (cmInput cm)
     ; when (cmDebug cm) $
         do { putStrLn "Source Program\n"
            ; pprint pgm
            ; putStrLn "--------------------------------\\"
            ; putStrLn "Flattened Program\n"
            ; pprint . D.flatten . D.pgmTerm $ pgm
            ; putStrLn "--------------------------------\\" }
     ; let !prog' = case cmML cm of
                      True -> ML.ppProgram . translateProgramCBV $ pgm
                      False -> H.ppProgram . (case cmLocal cm of
                                               True -> translateProgramLocal
                                               False -> translateProgramST) $ pgm
     ; case cmOutput cm of
         "-" -> putStrLn prog'
         fp  -> writeFile fp prog'
     }

runEvaluate :: EvalMode -> IO ()
runEvaluate em =
  do { term <- D.pgmTerm <$> getProgram (emInput em)
     ; when (emDebug em) $ pprint term
     ; putStr "> "
     ; print . D.evalEmpty $ term }

runTypeOf :: TypeMode -> IO ()
runTypeOf tm =
  do { pgm <- getProgram (tmInput tm)
     ; when (tmDebug tm) $ pprint pgm
     ; putStrLn . ppTypeScheme . inferTSProgram $ pgm }
