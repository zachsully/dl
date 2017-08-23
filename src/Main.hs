{-# LANGUAGE BangPatterns #-}
module Main where

import System.Environment (getArgs,getProgName)

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
     ; let prog = snd $ runState (parseProgram tokens) ([],[])
     ; print prog
     ; print (case prog of
                D.Program _ t -> D.evalStart t)
     ; putStrLn . H.ppProgram . translateProgram $ prog
     }

runTest :: String -> IO ()
runTest n =
  case lookup n tests of
    Just t -> putStrLn undefined
    Nothing -> putStrLn $ "no test named: " ++ n

tests = []
