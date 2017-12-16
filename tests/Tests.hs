{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit

import DualSyn
import Interpreter
import Judgement
import Utils
import IO
import Pretty

main :: IO ()
main =
  do { files ← getPgmFiles
     ; let num    = length files
           filesI = zip [1..num] files
     ; forM filesI $ \(i,fp) →
         do { putStrLn ("------------ (" <> show i <> "/" <> show num <> ")"
                        <+> fp <+> "------------")
            ; pgm ← getProgram ("examples" </> fp)
            ; putStrLn "Parses as:"
            ; pprint (pgmTerm pgm)
            ; putStrLn ""

            ; putStrLn "Has type:"
            ; case runStd (inferTSProgram pgm) of
                Left e → putStrLn e
                Right typ → pprint typ
            ; putStrLn ""

            ; putStrLn "Evaluates to:"
            ; case runStd (interpPgm pgm) of
                Left e → putStrLn e
                Right v → pprint v
            ; putStrLn ""
            }
     ; exitFailure }

getPgmFiles :: IO [FilePath]
getPgmFiles = filter ((==".dl"). takeExtension) <$> listDirectory "examples"
