{- |
Module      : DL.Pipelines
Description : Define all of the DL compilation and interpretation pipelines
-}
module DL.Pipelines where

-- external
import Control.Monad
import System.Exit
import System.IO

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
import DL.Flat.Syntax
import DL.Flat.Interpreter
import DL.Utils.Pretty
import DL.Utils.StdMonad
import DL.Utils.IO

parsePipe :: FilePath -> Bool -> IO (Program Term)
parsePipe fp debug =
  do { pgm <- getProgram fp
     ; when debug $
         do { putStrLn "====== Parsed ======"
            ; pprint pgm
            ; putStrLn "" }
     ; return pgm }

renamePipe :: Program Term -> Bool -> IO (Program Term)
renamePipe pgm debug =
  let pgm' = renamePgm pgm in
    do { when debug $
           do { putStrLn "====== Renamed ======="
              ; pprint pgm'
              ; putStrLn "" }
       ; return pgm' }

tcPipe :: Program Term -> Bool -> IO (Program Term)
tcPipe pgm debug =
  do { ety <- typeCheckPgm (TcConfig debug) pgm
     ; when debug $
         do { putStrLn "====== Type ======="
            ; putStrLn (either id pp ety)
            ; putStrLn "" }
     ; return pgm }

flattenPipe :: Program Term -> Bool -> IO (Program FlatTerm)
flattenPipe pgm debug =
  let pgm' = flattenPgm pgm in
    do { when debug $
           do { putStrLn "====== Flattened ======"
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
                      case runStd (interpPgm (flattenPgm (preludePgm t))) of
                        Left s -> hPutStrLn stdout $ s
                        Right a -> hPutStrLn stdout $ pp a
                          -- case runStd (infer [] (reifyValue a)) of
                          --   Left _ -> hPutStrLn stdout . pp $ a
                          --   Right ty -> hPutStrLn stdout $
                          --     pp a <+> ":" <+> pp ty
            }

     }

compilePipeline :: FilePath -> FilePath -> Bool -> Backend p -> IO ()
compilePipeline infp outfp _ bkd =
  let !prog' = runBackend bkd (undefined infp) in
    case outfp of
      "-" -> putStrLn prog'
      fp  -> writeFile fp prog'

tcPipeline :: FilePath -> Bool -> IO ()
tcPipeline fp debug =
  do { pgm <- getProgram fp
     ; when debug $
         do { putStrLn "====== Parsed ======"
            ; pprint pgm
            ; putStrLn "" }
     ; when debug (putStrLn "====== Type Checked ======")
     ; ety <- typeCheckPgm (TcConfig debug) pgm
     ; case ety of
         Left err -> putStrLn err >> exitWith (ExitFailure 1)
         Right ty -> pprint ty >> exitWith ExitSuccess }

evalPipeline :: FilePath -> Bool -> IO ()
evalPipeline fp _ =
  do { putStrLn "====== Evaluated ======"
     ; case runStd (interpPgm (undefined fp)) of
         Left s -> putStrLn s
         Right a -> putStrLn (pp a)
     }
