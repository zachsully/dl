{-# LANGUAGE BangPatterns #-}
module DL.Utils.IO where

import DL.Parser.Parser
import DL.Parser.Lexer
import DL.General.Top
import DL.Surface.Syntax

import System.Directory
import System.Exit
import System.Process
import Text.Read

--------------------------------------------------------------------------------
--                                 IO                                         --
--------------------------------------------------------------------------------

-- | Parse a `Program Term` from a `FilePath`
getProgram :: FilePath -> IO (Program Term)
getProgram fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; case tokens of
         Left e -> error e
         Right ts ->
           case runParserM (parseProgram ts) emptyPState of
             Left e -> error e
             Right (p,_) -> return p
     }

-- | Either parse or return error
getProgram' :: FilePath -> IO (Maybe (Program Term))
getProgram' fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; case tokens of
         Left e -> error e
         Right ts ->
           case runParserM (parseProgram ts) emptyPState of
             Left _      -> return Nothing
             Right (p,_) -> return (Just p)
     }


-- | For running programs with our different backends
interpretWith
  :: (Read a) -- ^ `a` is the type of the programs output
  => String   -- ^ Program as a string
  -> String   -- ^ Interpreter executable
  -> IO (Maybe a)
interpretWith prog interp =
  do { writeFile "temp.dl" prog
     ; (code,_,out) <- readProcessWithExitCode interp ["temp.dl"] ""
     ; let result = case code of
                      ExitFailure _ -> Nothing
                      ExitSuccess   -> readMaybe out
     ; removeFile "temp.dl"
     ; return result
     }
