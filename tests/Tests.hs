{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit

import DL.Syntax.Top
import DL.Evaluation.Interpreter
import DL.Judgement
import DL.Utils
import DL.IO
import DL.Pretty

main :: IO ()
main =
  do { files ← getPgmFiles
     ; let num    = length files
           filesI = zip [1..num] files
     ; errs <- foldM
         (\errs (i,fp) →
           do { putStrLn ("------------ (" <> show i <> "/" <> show num <> ")"
                          <+> fp <+> "------------")
              ; pgm ← getProgram ("examples/source" </> fp)
              ; putStrLn "Parses as:"
              ; pprint (pgmTerm pgm)
              ; putStrLn ""

              -- ; putStrLn "Has type:"
              -- ; case runStd (inferTSProgram pgm) of
              --     Left e → putStrLn e
              --     Right typ → pprint typ
              -- ; putStrLn ""

              ; putStrLn "Evaluates to:"
              ; case runStd (interpPgm pgm) of
                  Left e → putStrLn (e <> "\n") >> return (errs+1)
                  Right v → pprint v >> return errs
              })
         0
         filesI
     ; case errs of
         0 -> exitSuccess
         _ -> putStrLn (show errs <> "/" <> show num <+> " errors")
              >> exitFailure
     }

getPgmFiles :: IO [FilePath]
getPgmFiles = filter ((==".dl"). takeExtension)
          <$> listDirectory "examples/source"
