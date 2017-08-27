{-# LANGUAGE BangPatterns #-}
module Main where

import Data.Monoid
import Options.Applicative
import Control.Monad.State

-- local
import qualified DualSyn as D
import qualified HsSyn as H
import Lexer
import Parser
import Translation
import Judgement

data Mode
  = Compile FilePath FilePath
  | Evaluate FilePath
  | TypeOf FilePath
  deriving (Show,Eq)

inputFp :: Parser FilePath
inputFp = strArgument (metavar "INPUT" <> help "input dual language file")

parseCompile :: Parser Mode
parseCompile = Compile
           <$> inputFp
           <*> strArgument (metavar "OUTPUT" <> help "output Haskell file")

parseEvaluate :: Parser Mode
parseEvaluate = Evaluate <$> inputFp

parseTypeOf :: Parser Mode
parseTypeOf = TypeOf <$> inputFp

selectMode :: Parser Mode
selectMode =
  subparser $
    (command "compile" (info (helper <*> parseCompile)
                             (progDesc "compile a dual language program to Haskell")))
           <> (command "eval" (info (helper <*> parseEvaluate)
                              (progDesc "evaluate a dual language program")))
           <> (command "type" (info (helper <*> parseTypeOf)
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
              Compile inFp outFp -> runCompile inFp outFp
              Evaluate inFp -> runEvaluate inFp
              TypeOf inFp -> runTypeOf inFp
          }

getProgram :: FilePath -> IO D.Program
getProgram fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; return . fst . runState (parseProgram tokens) $ emptyState
     }

runCompile :: FilePath -> FilePath -> IO ()
runCompile inFp outFp =
  do { prog <- getProgram inFp
     ; let prog' = H.ppProgram . translateProgram $ prog
     ; case outFp of
         "-" -> putStrLn prog'
         _   -> writeFile outFp prog'
     }

runEvaluate :: FilePath -> IO ()
runEvaluate inFp = getProgram inFp >>= (print . D.evalStart . D.pgmTerm)

runTypeOf :: FilePath -> IO ()
runTypeOf inFp = getProgram inFp >>= (print . typeOfProgram)
