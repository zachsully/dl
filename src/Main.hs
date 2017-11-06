{-# LANGUAGE BangPatterns #-}
module Main where

import Data.Monoid
import Options.Applicative
import Control.Monad.State
import Control.Monad (when)

-- local
import Syntax.Dual
import qualified Syntax.Hs as H
import qualified Syntax.ML as ML
import Parser.Lexer
import Parser.Parser
import Translation
import Interp
-- import Judgement
import Pretty


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

getProgram :: FilePath -> IO (Program Term)
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
     ; putStrLn "\n->>R\n"
     ; pprint . flatten . pgmTerm $ pgm
     }

runCompile :: CompileMode -> IO ()
runCompile cm =
  do { pgm <- getProgram (cmInput cm)
     ; let pgm' = flattenPgm pgm
     ; when (cmDebug cm) $
         do { pprint pgm
            ; putStrLn "\n->>R\n"
            ; pprint pgm'
            ; putStrLn "\n=>\n" }
     ; let !prog' = case cmML cm of
                      True -> ML.ppProgram . translateProgramCBV $ pgm'
                      False -> H.ppProgram . (case cmLocal cm of
                                               True -> translateProgramLocal
                                               False -> translateProgramST) $ pgm'
     ; case cmOutput cm of
         "-" -> putStrLn prog'
         fp  -> writeFile fp prog'
     }

runEvaluate :: EvalMode -> IO ()
runEvaluate em =
  do { term <- pgmTerm <$> getProgram (emInput em)
     ; when (emDebug em) $ pprint term
     ; putStr "> "
     ; pprint . evalEmpty $ term }

runTypeOf :: TypeMode -> IO ()
runTypeOf tm = error "unimplemented"
  -- do { pgm <- getProgram (tmInput tm)
  --    ; when (tmDebug tm) $ pprint pgm
  --    ; putStrLn . ppTypeScheme . inferTSProgram $ pgm }
