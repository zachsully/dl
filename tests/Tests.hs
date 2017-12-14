{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import System.FilePath
import System.Directory
import System.Exit

import Utils
import IO
import Pretty

main :: IO ()
main =
  do { files ← getPgmFiles
     ; forM files $ \fp →
         do { putStrLn ("<test-file>:" <+> fp)
            ; pgm ← getProgram ("examples" </> fp)
            ; putStrLn ""
            }
     ; exitSuccess }

getPgmFiles :: IO [FilePath]
getPgmFiles = filter ((==".dl"). takeExtension) <$> listDirectory "examples"
