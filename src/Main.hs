{-# LANGUAGE BangPatterns #-}
module Main where

import System.Environment (getArgs,getProgName)

import DualSyn
import Syn
import Translation

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
  do { !contents <- case fp of
                      "-" -> getContents
                      _   -> readFile fp
     ; return ()
     -- ; case parseSrc contents of
     --     Left err  -> putStrLn err
     --     Right src -> putStrLn . ppSrc . translate $ src
     }

runTest :: String -> IO ()
runTest n =
  case lookup n tests of
    Just t -> putStrLn . ppSrc $ (translate t)
    Nothing -> putStrLn $ "no test named: " ++ n

--------------------------------------------------------------------------------
--                                 Examples                                   --
--------------------------------------------------------------------------------

tests :: [(String,Src CoDataDcl Observation)]
tests = [("stream",testStream)
        ,("state",testState)]

testStream :: Src CoDataDcl Observation
testStream = SrcDcl $
  CoData "Stream" ["a"]
    [ CoPattern "Head"
        (TyArr (TyApp (TyVar "Stream") (TyVar "a"))
               (TyVar "a"))
    , CoPattern "Tail"
        (TyArr (TyApp (TyVar "Stream") (TyVar "a"))
               (TyApp (TyVar "Stream") (TyVar "a")))
    ]

testState :: Src CoDataDcl Observation
testState = SrcDcl $
  CoData "State" ["s","a"]
    [ CoPattern "Get"
        (TyArr (TyApp (TyApp (TyVar "State") (TyVar "s"))
                             (TyVar "a"))
               (TyArr (TyVar "s")
                      (TyVar "s")))
    , CoPattern "Put"
        (TyArr (TyApp (TyApp (TyVar "State") (TyVar "s"))
                             (TyVar "a"))
               (TyArr (TyVar "s")
                      (TyVar "()")))
    ]
