module Main where

import Data.Monoid
import Options.Applicative
import Control.Monad.State
import Control.Monad (when)
import System.IO

-- local
import qualified DL.Syntax.Term as D
import DL.Flatten
import qualified DL.Backend.Haskell.Syntax as H
import qualified DL.Backend.ML.Syntax as ML
import qualified DL.Backend.Racket.Syntax as Rkt
import DL.Parser.Lexer
import DL.Parser.Parser
import DL.Translation
import DL.Interpreter
import DL.Judgement
import DL.Utils
import DL.Pretty
import DL.IO

--------------------------------------------------------------------------------
--                              Cmdline Options                               --
--------------------------------------------------------------------------------

data FlattenMode
  = FlattenMode { fmInput :: FilePath }

data Strategy = CallByName | CallByValue

data CompileMode
  = CompileMode
  { cmDebug   :: Bool
  , cmStrat   :: Strategy
  , cmUntyped :: Bool
  , cmInput   :: FilePath
  , cmOutput  :: FilePath }

data EvalMode
  = EvalMode
  { emDebug  :: Bool
  , emInput  :: FilePath }

data TypeMode
  = TypeMode
  { tmDebug  :: Bool
  , tmBidir  :: Bool
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
           <*> argument (str >>= \s ->
                            case s of
                              "call-by-value" -> return CallByValue
                              "call-by-name" -> return CallByName
                              _ -> readerError (s <+> "is not a valid evaluation strategy.")
                        )
                        (   metavar "STRATEGY"
                         <> help "specify 'call-by-value' or 'call-by-name' evaluation strategy")
           <*> switch (  long "untyped"
                      <> help "compile to an untyped language" )
           <*> inputFp
           <*> strArgument (metavar "OUTPUT" <> help "output source file")

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
           <*> switch (  long "bidir"
                      <> short 'B'
                      <> help "use bidirectional type checking instead DHM type inference." )
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
main = do { mode <- parseMode
          ; case mode of
              Flatten fm  -> runFlatten fm =<< getProgram (fmInput fm)
              Compile cm  -> runCompile cm =<< getProgram (cmInput cm)
              Evaluate em -> runEvaluate em =<< getProgram (emInput em)
              TypeOf tm   -> runTypeOf tm =<< getProgram (tmInput tm)
              Repl        -> runRepl
          }

runFlatten :: FlattenMode -> D.Program D.Term -> IO ()
runFlatten _ pgm =
  do { pprint pgm
     ; putStrLn "\n->>R\n"
     ; pprint . flatten . D.pgmTerm $ pgm }

runCompile :: CompileMode -> D.Program D.Term -> IO ()
runCompile cm pgm =
  let pgm' = flattenPgm pgm in
    do { when (cmDebug cm) $
         do { pprint pgm
            ; putStrLn "\n->>R\n"
            ; pprint pgm'
            ; putStrLn "\n=>\n" }
       ; let !prog' = (case (cmStrat cm,cmUntyped cm) of
                         (CallByName,False)  -> (pp :: H.Program -> String) . translate
                         (CallByName,True)   -> error "not existing call-by-name untyped translation"
                         (CallByValue,False) -> (pp :: ML.Program -> String) . translate
                         (CallByValue,True)  -> (pp :: Rkt.Program -> String) . translate)

                    $ pgm'
       ; case cmOutput cm of
           "-" -> putStrLn prog'
           fp  -> writeFile fp prog'
       }

runEvaluate :: EvalMode -> D.Program D.Term -> IO ()
runEvaluate em pgm =
  let term = D.pgmTerm pgm in
    do { when (emDebug em) $ pprint term
       ; putStr "> "
       ; case runStd (interpEmpty term) of
           Left s -> print s
           Right a -> pprint a
       }

runTypeOf :: TypeMode -> D.Program D.Term -> IO ()
runTypeOf tm pgm =
  do { when (tmDebug tm) $ print pgm
     ; case tmBidir tm of
         True ->
           case runStd . typeOfProgram $ pgm of
             Left e -> putStrLn e
             Right ty -> putStrLn . pp $ ty
         False ->
           case runStd . inferTSProgram $ pgm of
             Left e -> putStrLn e
             Right ty -> putStrLn . pp $ ty
     }

runRepl :: IO ()
runRepl =
  do { hSetBuffering stdout NoBuffering
     ; hSetBuffering stdin  LineBuffering
     ; forever $
         do { hPutStr stdout "▪ "
            ; m <- lexString <$> hGetLine stdin
            ; case m of
                Left e -> hPutStrLn stdout e
                Right ts ->
                  case runParserM (parseTerm ts) emptyState of
                    Left e -> hPutStrLn stdout e
                    Right (t,_) ->
                      case runStd (interpEmpty (D.Prompt t)) of
                        Left s -> hPutStrLn stdout $ s
                        Right a ->
                          case runStd (infer [] (reifyValue a)) of
                            Left _ -> hPutStrLn stdout . pp $ a
                            Right ty -> hPutStrLn stdout $
                              pp a <+> ":" <+> pp ty
            }
     }
