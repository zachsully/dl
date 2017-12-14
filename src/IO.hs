{-# LANGUAGE BangPatterns #-}
module IO where

import DualSyn
import Parser
import Lexer

--------------------------------------------------------------------------------
--                                 IO                                         --
--------------------------------------------------------------------------------

getProgram :: FilePath -> IO (Program Term)
getProgram fp =
  do { !tokens <- case fp of
                    "-" -> lexContents
                    _   -> lexFile fp
     ; case tokens of
         Left e -> error e
         Right ts ->
           case runParserM (parseProgram ts) emptyState of
             Left e -> error e
             Right (p,_) -> return p
     }
