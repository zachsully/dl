{-# LANGUAGE BangPatterns #-}
{- |
Module      : Main
Description : Handles command line parsing and calling of compilers
-}
module Main where

import Text.Read (readMaybe)
import Options.Applicative

-- local
import DL.Backend
import DL.Flat.Backends
import DL.Pipelines
import DL.Flat.Syntax
import DL.Utils.Pretty
import DL.General.Strategy

--------------------------------------------------------------------------------
--                              Cmdline Options                               --
--------------------------------------------------------------------------------

data FlattenMode
  = FlattenMode { fmInput :: FilePath }

data CompileMode
  = CompileMode
  { cmDebug   :: Bool
  , cmBackend :: Backend FlatTerm
  , cmInput   :: FilePath
  , cmOutput  :: FilePath }

data EvalMode
  = EvalMode
  { emDebug  :: Bool
  , emStrat  :: Strategy
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
  | Repl

inputFp :: Parser FilePath
inputFp = strArgument (metavar "INPUT" <> help "input dual language file")

parseFlatten :: Parser FlattenMode
parseFlatten = FlattenMode <$> inputFp

parseCompile :: Parser CompileMode
parseCompile = CompileMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> argument (str >>= \s -> return $
                            case (readMaybe s) :: Maybe Int of
                              Just 0 -> hsCompile
                              Just 1 -> mlCompile
                              Just 2 -> rktCompile
                              Just 3 -> jsCompile
                              _ -> error (s <+> "is not a valid backend")
                        )
                        (   metavar "BACKEND"
                         <> help "0 -> Haskell\n1 -> Ocaml\n2 -> Racket\n3 -> JavaScript")
           <*> inputFp
           <*> strArgument (metavar "OUTPUT" <> help "output source file")

parseEvaluate :: Parser EvalMode
parseEvaluate = EvalMode
           <$> switch (  long "debug"
                      <> short 'D'
                      <> help "debug mode" )
           <*> argument (str >>= \s -> return $
                            case s of
                              "cbn" -> CallByName
                              "cbv" -> CallByValue
                              _ -> error (s <+> "is not a valid strategy. It must be either 'cbn' or 'cbv'")
                        )
                        (   metavar "STRATEGY"
                         <> help "either 'cbn' or 'cbv'")
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
  <> (command "repl" (info (helper <*> (pure Repl))
                           (progDesc "a dl read-eval-print loop.")))
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
main =
  do { mode <- parseMode
     ; case mode of
         Flatten fm  -> stdPipeline (fmInput fm) True >> return ()
         Compile cm  -> compilePipeline (cmInput cm) (cmOutput cm) (cmDebug cm) (cmBackend cm)
         Evaluate em -> evalPipeline (emStrat em) (emInput em) (emDebug em)
         TypeOf tm   -> tcPipeline (tmInput tm) (tmDebug tm)
         Repl        -> repl
     }
