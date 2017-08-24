{-# LANGUAGE BangPatterns #-}
module Main where

import Control.Monad.State
import System.Environment (getArgs,getProgName)

-- local
import qualified DualSyn as D
import qualified HsSyn as H
import Lexer
import Parser
import Translation
import Judgement

--------------------------------------------------------------------------------
--                                   Main                                     --
--------------------------------------------------------------------------------

main :: IO ()
main =
  do { args <- getArgs
     ; case args of
         ("test":n:[]) -> runTest n
         (fp:[]) -> runPreprocessor fp
         _ -> getProgName >>= \p -> putStrLn ("Usage: " ++ p ++ " *.cohs")
     }

runPreprocessor :: FilePath -> IO ()
runPreprocessor fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; let prog = fst . runState (parseProgram tokens) $ []
     ; putStr "\nProgram:\n"
     ; print prog
     ; putStr "\nEvaluates:\n"
     ; print (case prog of
                D.Program _ t -> D.evalStart t)
     ; putStr "\nTranslation:\n"
     ; putStrLn . H.ppProgram . translateProgram $ prog
     }

runTest :: String -> IO ()
runTest n =
  case lookup n tests of
    Just t -> putStrLn undefined
    Nothing -> putStrLn $ "no test named: " ++ n

tests = []
