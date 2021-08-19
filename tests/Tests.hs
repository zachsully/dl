module Main where

import Control.Monad
import Data.List
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit
import Text.Read

import DL.Backend
import DL.Flat.Backend.JavaScript
import DL.Flat.Backend.ML
import DL.Flat.Backend.Racket
import DL.Flat.Backend.Haskell
import DL.General.Strategy
import DL.General.Top
import qualified DL.General.Type as Ty
import DL.Flat.Syntax
import DL.Flat.Interpreter
import qualified DL.Flat.Syntax as F
import DL.Surface.Syntax
import DL.Surface.Typecheck
import DL.Surface.Flatten
import DL.Utils.StdMonad
import DL.Utils.IO
import DL.Utils.Pretty

expectedTypeErrors,expectedOutputErrors :: Int
expectedTypeErrors = 3
expectedOutputErrors = 10

main :: IO ()
main =
  do { cases <- mapM (\p -> testFile p >>= \c -> pprint c >> return c) =<< getPgmFiles
     ; report cases }
  where report cases =
          let n = length cases
              unexpectedTypeError = sum (fmap (\c ->
                                                 case (tsurface c,tTy c) of
                                                   (Just _, Nothing) ->
                                                     case tbehavior c of
                                                       Just ThrowsTypeError -> 0
                                                       _ -> 1
                                                   _ -> 0)
                                              cases)
              badOutput = sum (fmap (\c ->
                                       case (tsurface c,tflat c,tevalCBNOut c) of
                                         (Just _,Just _, Just i) ->
                                           case tbehavior c of
                                             Just (Computes j) ->
                                               if i == j then 0 else 1
                                             _ -> 0
                                         _ -> 0 )
                                    cases)
          in do { putStrLn ("Unexpected type error:" <+> show unexpectedTypeError <> "/" <> show n)
                ; putStrLn ("Bad output:" <+> show badOutput <> "/" <> show n)
                ; when (unexpectedTypeError /= expectedTypeErrors) $
                    do { putStrLn ("Expected" <+> show expectedTypeErrors <+> "type errors")
                       ; exitWith (ExitFailure 1) }
                ; when (badOutput /= expectedOutputErrors) $
                    do { putStrLn ("Expected" <+> show expectedTypeErrors <+> "output errors")
                       ; exitWith (ExitFailure 2) }
                ; exitWith ExitSuccess }

getPgmFiles :: IO [FilePath]
getPgmFiles = (sort . fmap ("examples/"++) . filter ((==".dl") . takeExtension))
          <$> listDirectory "examples/"

-- | Holds information for a particular test
data TestCase
  = TestCase
  { tfile       :: FilePath
  , tbehavior   :: Maybe Behavior
  , tsurface    :: Maybe (Program Term)
  , tTy         :: Maybe Ty.Type
  , tflat       :: Maybe (Program FlatTerm)
  , tevalCBNOut :: Maybe Int
  , tevalCBVOut :: Maybe Int
  , thsOut      :: Maybe Int
  , tmlOut      :: Maybe Int
  , trktOut     :: Maybe Int
  , tjsOut      :: Maybe Int
  }

instance Pretty TestCase where
  pp test = vmconcat
    [ "===============" <+> tfile test <+> "==============="
    , "did parse?        " <+> maybe "false" (const "true") (tsurface test)
    , "type?             " <+> ppMaybe (tTy test)
    , "expected behavior?" <+> maybe "Undefined" show (tbehavior test)
    , "eval output?      " <+> maybe "none" (\n -> "some" <> DL.Utils.Pretty.parens (show n)) (tevalCBNOut test)
    , "", ""
    ]

testFile :: FilePath -> IO TestCase
testFile fp =
  do { mpgm <- getProgram' fp
     ; let mbehavior = fmap (mdExpectedBehavior . pgmMetadata) mpgm
     ; ty <- case mpgm of
               Nothing -> return Nothing
               Just p ->
                 do { e <- typeCheckPgm (TcConfig False) p
                    ; case e of
                        Left _ -> return Nothing
                        Right x -> return (Just x)
                    }
     ; let fpgm = flattenPgm <$> mpgm
     ; let cbnOut = runInterp CallByName =<< fpgm
     ; let cbvOut = runInterp CallByValue =<< fpgm
     -- ; mhs  <- runIfJust (fmap interpHaskell fpgm)
     -- ; mml  <- runIfJust (fmap interpOcaml fpgm)
     -- ; mrkt <- runIfJust (fmap interpRacket fpgm)
     -- ; mjs  <- runIfJust (fmap interpJS fpgm)
     ; return (TestCase { tfile       = fp
                        , tbehavior   = mbehavior
                        , tsurface    = mpgm
                        , tTy         = ty
                        , tflat       = fpgm
                        , tevalCBNOut = cbnOut
                        , tevalCBVOut = cbvOut
                        , thsOut      = Nothing
                        , tmlOut      = Nothing
                        , trktOut     = Nothing
                        , tjsOut      = Nothing })
     }
  where runIfJust :: Maybe (IO (Maybe a)) -> IO (Maybe a)
        runIfJust Nothing  = return Nothing
        runIfJust (Just i) = i
        runInterp :: Strategy -> Program FlatTerm -> Maybe Int
        runInterp strat t =
          case runStd (interpPgm CallByName False t) of
            Right (_,FLit i) -> Just i
            _ -> Nothing

-- | Different interpreters for the backends
interpHaskell,interpRacket,interpOcaml,interpJS
  :: Program FlatTerm -> IO (Maybe Int)
interpHaskell prog = interpretWith (runBackend hsCompile prog) "runhaskell"
interpRacket  prog = interpretWith (runBackend rktCompile prog) "racket"
interpOcaml   prog = interpretWith (runBackend mlCompile prog) "ocaml"
interpJS      prog = interpretWith (runBackend jsCompile prog) "node"
