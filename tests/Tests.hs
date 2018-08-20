{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit
import Text.Read

import qualified DL.Syntax.Flat as F
import qualified DL.Backend.JavaScript.Syntax as JS
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Flat
import DL.Evaluation.Interpreter
import DL.Judgement
import DL.Utils
import DL.IO
import DL.Pretty
import DL.Translation
import qualified DL.Backend.Haskell.Syntax as H
import qualified DL.Backend.ML.Syntax      as ML
import qualified DL.Backend.Racket.Syntax  as Rkt

-- | Holds information for a particular test
data TestCase
  = TestCase
  { tfile   :: FilePath
    -- | Expected output, if available. For now tests must output ints
  , toutput :: Maybe Int
    -- | Parser output
  , tpgm    :: Maybe (Program Term)
    -- | Flattening output
  , tfpgm   :: Maybe (Program FlatTerm)
    -- | Evalutation output
  , teval   :: Maybe Int
    -- | Haskell backend output
  , ths     :: Maybe Int
    -- | Ocaml backend output
  , tml     :: Maybe Int
    -- | Racket backend output
  , trkt    :: Maybe Int
    -- | Javascript backend output
  , tjs     :: Maybe Int
  }

main :: IO ()
main = mapM_ testFile =<< getPgmFiles

getPgmFiles :: IO [FilePath]
getPgmFiles = (fmap ("examples/source/"++) . filter ((==".dl") . takeExtension))
          <$> listDirectory "examples/source"

testFile :: FilePath -> IO TestCase
testFile fp =
  do { putStrLn fp

     ; mpgm <- getProgram' fp
     ; printRes "parse" False mpgm

     ; mout <- getProgramOutput fp
     ; printRes "contain output" True mout

     ; let fpgm = fmap flattenPgm mpgm

     ; mhs <- runIfJust (fmap interpHaskell fpgm)
     ; printRes "Haskell output" True mhs

     ; mml <- runIfJust (fmap interpOcaml fpgm)
     ; printRes "Ocaml output" True mml

     ; mrkt <- runIfJust (fmap interpRacket fpgm)
     ; printRes "Racket output" True mrkt

     ; putStrLn ""

     ; return (TestCase { tfile   = fp
                        , toutput = mout
                        , tpgm    = mpgm
                        , tfpgm   = fpgm
                        , teval   = Nothing
                        , ths     = mhs
                        , tml     = mml
                        , trkt    = mrkt
                        , tjs     = Nothing })
     }
  where printRes :: Show a => String -> Bool -> Maybe a -> IO ()
        printRes verb _ Nothing = putStrLn (indent 2 ("failed to" <+> verb))
        printRes verb True (Just a) =  putStrLn (indent 2 (verb <+> "with" <+> show a))
        printRes _ _ _ = return ()

        runIfJust :: Maybe (IO (Maybe a)) -> IO (Maybe a)
        runIfJust Nothing  = return Nothing
        runIfJust (Just i) = i

getProgramOutput :: FilePath -> IO (Maybe Int)
getProgramOutput fp =
  do { exists <- doesFileExist fp
     ; case exists of
         False -> return Nothing
         True ->
           do { prog <- lines <$> readFile fp
              ; case prog of
                  (l:_) ->
                    case l of
                      '-':'-':'o':xs -> return (readMaybe xs)
                      _ -> return Nothing
                  _ -> return Nothing
              }
     }


-- | Different interpreters for the backends
interpHaskell,interpRacket,interpOcaml
  :: Program FlatTerm -> IO (Maybe Int)

interpHaskell prog =
  let s = (pp :: H.Program -> String) . translate $ prog in
    interpretWith s "runhaskell"

interpRacket  prog =
  let s = (pp :: Rkt.Program -> String) . translate $ prog in
    interpretWith s "racket"

interpOcaml   prog =
  let s = (pp :: ML.Program -> String) . translate $ prog in
    interpretWith s "ocaml"

-- interpJS      prog = interpretWith prog "node"
