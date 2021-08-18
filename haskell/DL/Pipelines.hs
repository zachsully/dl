{-# LANGUAGE BangPatterns #-}
{- |
Module      : DL.Pipelines
Description : Define all of the DL compilation and interpretation pipelines
-}
module DL.Pipelines where

-- external
import Control.Monad
import System.Exit
import System.IO
import Prelude hiding (log)

-- local
import DL.Backend
import DL.Parser.Lexer
import DL.Parser.Parser
import DL.Surface.Syntax
import DL.Surface.Rename
import DL.Surface.Typecheck
import DL.Surface.Flatten
import DL.Surface.Prelude
import DL.General.Top
import DL.General.Strategy
import DL.Flat.Syntax
import DL.Flat.Interpreter
import DL.Utils.Pretty
import DL.Utils.StdMonad
import DL.Utils.IO

parsePipe :: Bool -> FilePath -> IO (Program Term)
parsePipe debug fp =
  do { pgm <- getProgram fp
     ; when debug $
         do { putStrLn (mkBf "====== Parsed ======")
            ; pprint pgm
            ; putStrLn "" }
     ; return pgm }

renamePipe :: Bool -> Program Term -> IO (Program Term)
renamePipe debug pgm =
  let pgm' = renamePgm pgm in
    do { when debug $
           do { putStrLn (mkBf "====== Renamed =======")
              ; pprint pgm'
              ; putStrLn "" }
       ; return pgm' }

tcPipe :: Bool -> Program Term -> IO (Program Term)
tcPipe debug pgm =
  do { ety <- typeCheckPgm (TcConfig debug) pgm
     ; when debug $
         do { putStrLn (mkBf "====== Type =======")
            ; case ety of
                Left err -> putStrLn err >> exitWith (ExitFailure 1)
                Right ty -> putStrLn (pp ty)
            ; putStrLn "" }
     ; return pgm }

flattenPipe :: Bool -> Program Term -> IO (Program FlatTerm)
flattenPipe debug pgm =
  let pgm' = flattenPgm pgm in
    do { when debug $
           do { putStrLn (mkBf "====== Flattened ======")
              ; pprint pgm'
              ; putStrLn "" }
       ; return pgm' }

stdPipeline :: FilePath -> Bool -> IO (Program FlatTerm)
stdPipeline _fp _debug = undefined

coreDataPipeline :: FilePath -> Bool -> IO ()
coreDataPipeline = undefined

coreCodataPipeline :: FilePath -> Bool -> IO ()
coreCodataPipeline = undefined

repl :: IO ()
repl =
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
                      case runStd (interpPgm CallByName False (flattenPgm (preludePgm t))) of
                        Left s -> hPutStrLn stdout $ s
                        Right a -> hPutStrLn stdout $ pp (snd a)
                          -- case runStd (infer [] (reifyValue a)) of
                          --   Left _ -> hPutStrLn stdout . pp $ a
                          --   Right ty -> hPutStrLn stdout $
                          --     pp a <+> ":" <+> pp ty
            }

     }

compilePipeline :: FilePath -> FilePath -> Bool -> Backend FlatTerm -> IO ()
compilePipeline infp outfp debug bkd =
  parsePipe debug infp
    >>= renamePipe debug . addPrelude
    >>= tcPipe debug
    >>= flattenPipe debug
    >>= outfn . runBackend bkd
  where outfn :: String -> IO ()
        outfn = case outfp of
                  "-" -> putStrLn
                  fp  -> writeFile fp

tcPipeline :: FilePath -> Bool -> IO ()
tcPipeline fp debug =
  do { pgm <- getProgram fp
     ; when debug $
         do { putStrLn (mkBf "====== Parsed ======")
            ; pprint pgm
            ; putStrLn "" }
     ; when debug (putStrLn (mkBf "====== Type Checked ======"))
     ; ety <- typeCheckPgm (TcConfig debug) pgm
     ; case ety of
         Left err -> putStrLn err >> exitWith (ExitFailure 1)
         Right ty -> pprint ty >> exitWith ExitSuccess }

evalPipeline :: Strategy -> FilePath -> Bool -> IO ()
evalPipeline strat fp debug =
  do { pgm <- parsePipe debug fp
     ; pgm' <- flattenPipe debug =<< tcPipe debug =<< renamePipe debug (addPrelude pgm)
     ; putStrLn (mkBf "====== Evaluated ======")
     ; let (log,er) = runStdWithLog (interpPgm strat debug pgm')
     ; when debug (putStrLn (stringmconcat "\n---------------------\n" log))
     ; case er of
         Left s -> putStrLn s
         Right (i,a) -> putStrLn (("<steps taken>:" <+> show i) <->
                                  "<output>:" <+> (pp a))
     }
