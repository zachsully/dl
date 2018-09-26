module Main where

import Options.Applicative
import Control.Monad.State
import Control.Monad (when)
import System.IO
import System.Exit

-- local
import qualified DL.Syntax.Term            as T
import qualified DL.Syntax.Type            as Ty
import qualified DL.Syntax.Top             as Top
import DL.Backend
import DL.Backend.Haskell
import DL.Backend.ML
import DL.Backend.Racket
import DL.Backend.JavaScript
import DL.Syntax.Flat
import DL.Prelude
import DL.Parser.Lexer
import DL.Parser.Parser
import DL.Evaluation.Strategy
import DL.Evaluation.Interpreter
import DL.Rename
import DL.Typecheck
import DL.Utils
import DL.Pretty
import DL.IO

--------------------------------------------------------------------------------
--                              Cmdline Options                               --
--------------------------------------------------------------------------------

data FlattenMode
  = FlattenMode { fmInput :: FilePath }

data CompileMode
  = CompileMode
  { cmDebug   :: Bool
  , cmStrat   :: Strategy
  , cmUntyped :: Bool
  , cmOO      :: Bool
  , cmInput   :: FilePath
  , cmOutput  :: FilePath }

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
           <*> switch (  long "oo"
                      <> help "compile to an object-oriented language" )
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
              Flatten fm  -> stdPipeline (fmInput fm) True >> return ()
              Compile cm  -> runCompile cm =<< stdPipeline (cmInput cm) (cmDebug cm)
              Evaluate em -> runEvaluate em =<< stdPipeline (emInput em) (emDebug em)
              TypeOf tm   -> runTypeOf tm
              Repl        -> runRepl
          }

stdPipeline :: FilePath -> Bool -> IO (Top.Program FlatTerm, Ty.Type)
stdPipeline fp debug =
  do { pgm <- getProgram fp
     ; when debug $
         do { putStrLn "====== Parsed ======"
            ; pprint pgm
            ; putStrLn "" }
     ; let pgm' :: Top.Program T.Term
           pgm' = renamePgm pgm
     ; ety <- typeCheckPgm (TcConfig debug) pgm
     ; when debug $
         do { putStrLn "====== Renamed ======="
            ; pprint pgm'
            ; putStrLn "" }
     ; let pgm'' :: Top.Program FlatTerm
           pgm'' = flattenPgm pgm'
     ; when debug $
         do { putStrLn "====== Flattened ======"
            ; pprint pgm''
            ; putStrLn "" }
     ; case ety of
         Right ty -> return (pgm'',ty)
         Left e -> putStrLn e >> exitWith (ExitFailure 1)
     }

runCompile :: CompileMode -> (Top.Program FlatTerm,Ty.Type) -> IO ()
runCompile cm (pgm,_) =
  let !prog' = (case (cmStrat cm,cmUntyped cm,cmOO cm) of
                  (CallByName,False,False)  -> runBackend hsCompile
                  (CallByName,True,False)   -> error "not existing call-by-name untyped translation"
                  (CallByValue,False,False) -> runBackend mlCompile
                  (CallByValue,True,False)  -> runBackend rktCompile
                  (CallByValue,True,True)   -> runBackend jsCompile
                  (_,_,True)                -> error "not existing object oriented translation")
               $ pgm in
    case cmOutput cm of
      "-" -> putStrLn prog'
      fp  -> writeFile fp prog'

runEvaluate :: EvalMode -> (Top.Program FlatTerm,Ty.Type) -> IO ()
runEvaluate _ (pgm,ty) =
  do { putStrLn "====== Evaluated ======"
     ; case runStd (interpPgm pgm) of
         Left s -> putStrLn s >> putStrLn (pp ty)
         Right a -> putStrLn (pp a <+> ":" <+> pp ty)
     }

runTypeOf :: TypeMode -> IO ()
runTypeOf tm =
  do { pgm <- getProgram (tmInput tm)
     ; when (tmDebug tm) $
         do { putStrLn "====== Parsed ======"
            ; pprint pgm
            ; putStrLn "" }
     ; when (tmDebug tm) (putStrLn "====== Type Checked ======")
     ; ety <- typeCheckPgm (TcConfig (tmDebug tm)) pgm
     ; case ety of
         Left err -> putStrLn err >> exitWith (ExitFailure 1)
         Right ty -> pprint ty >> exitWith ExitSuccess }

runRepl :: IO ()
runRepl =
  do { hSetBuffering stdout NoBuffering
     ; hSetBuffering stdin  LineBuffering
     ; forever $
         do { hPutStr stdout "# "
            ; m <- lexString <$> hGetLine stdin
            ; case m of
                Left e -> hPutStrLn stdout e
                Right ts ->
                  case runParserM (parseTerm ts) (pStateFromDecls prelude) of
                    Left e -> hPutStrLn stdout e
                    Right (t,_) ->
                      case runStd (interpPgm (flattenPgm (preludePgm t))) of
                        Left s -> hPutStrLn stdout $ s
                        Right a -> hPutStrLn stdout $ pp a
                          -- case runStd (infer [] (reifyValue a)) of
                          --   Left _ -> hPutStrLn stdout . pp $ a
                          --   Right ty -> hPutStrLn stdout $
                          --     pp a <+> ":" <+> pp ty
            }

     }
