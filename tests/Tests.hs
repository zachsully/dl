module Main where

import Control.Monad
import Data.List
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit
import Text.Read

import DL.Backend
import DL.Backend.JavaScript
import DL.Backend.ML
import DL.Backend.Racket
import DL.Backend.Haskell
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
expectedOutputErrors = 1

-- | Holds information for a particular test
data TestCase
  = TestCase
  { tfile     :: FilePath
    -- | Expected behavior
  , tbehavior :: Maybe Behavior
    -- | Parser output
  , tpgm      :: Maybe (Program Term)
    -- | Type checker output
  , pgmTy     :: Maybe Ty.Type
    -- | Flattening output
  , tfpgm     :: Maybe (Program FlatTerm)
    -- | Evalutation output
  , teval     :: Maybe Int
    -- | Haskell backend output
  , ths       :: Maybe Int
    -- | Ocaml backend output
  , tml       :: Maybe Int
    -- | Racket backend output
  , trkt      :: Maybe Int
    -- | Javascript backend output
  , tjs       :: Maybe Int
  }

instance Pretty TestCase where
  pp (TestCase
      { tfile     = f
      , tbehavior = b
      , tpgm      = p
      , pgmTy     = t
      , tfpgm     = p'
      , teval     = e
      , ths       = h
      , tml       = m
      , trkt      = r
      , tjs       = j })
    = vmconcat
    [ "===============" <+> f <+> "==============="
    , "did parse?        " <+> (case p of
                          Nothing -> "false"
                          Just _ -> "true"
                       )
    , "type?             " <+> ppMaybe t
    , "expected behavior?" <+> (case b of
                                  Just a -> show a
                                  Nothing -> "Undefined"
                               )
    , "eval output?      " <+> (case e of
                            Nothing -> "none"
                            Just n -> "some" <> DL.Utils.Pretty.parens (show n)
                         )
    , "", ""
    ]

main :: IO ()
main =
  do { cases <- mapM (\p -> testFile p >>= \c -> pprint c >> return c) =<< getPgmFiles
     ; report cases }
  where report cases =
          let n = length cases
              failedToType = foldr (\c a ->
                                      case (do { _ <- tpgm c
                                               ; pgmTy c }) of
                                        Nothing ->
                                          case tbehavior c of
                                            Just ThrowsTypeError -> a
                                            _ -> a + 1
                                        Just _ -> a
                                   ) 0 cases
              badOutput = foldr (\c a ->
                                      case (do { _ <- tpgm c
                                               ; actual <- teval c
                                               ; case tbehavior c of
                                                   Just (Computes expected) -> return (expected == actual)
                                                   _ -> Nothing
                                               }) of
                                        Nothing -> a
                                        Just True -> a
                                        Just False -> a + 1
                                   ) 0 cases
          in do { putStrLn ("Failed to type:" <+> show failedToType <> "/" <> show n)
                ; putStrLn ("Bad output:" <+> show badOutput <> "/" <> show n)
                ; when (failedToType /= expectedTypeErrors) $
                    do { putStrLn ("Expected" <+> show expectedTypeErrors <+> "type errors")
                       ; exitWith (ExitFailure 1) }
                ; when (badOutput /= expectedOutputErrors) $
                    do { putStrLn ("Expected" <+> show expectedTypeErrors <+> "output errors")
                       ; exitWith (ExitFailure 2) }
                ; exitWith ExitSuccess }

getPgmFiles :: IO [FilePath]
getPgmFiles = (sort . fmap ("examples/source/"++) . filter ((==".dl") . takeExtension))
          <$> listDirectory "examples/source"

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
     ; let fpgm = fmap flattenPgm mpgm
     ; let me = join (fmap interp fpgm)
     ; mhs  <- runIfJust (fmap interpHaskell fpgm)
     ; mml  <- runIfJust (fmap interpOcaml fpgm)
     ; mrkt <- runIfJust (fmap interpRacket fpgm)
     ; mjs  <- runIfJust (fmap interpJS fpgm)
     ; return (TestCase { tfile     = fp
                        , tbehavior = mbehavior
                        , tpgm      = mpgm
                        , pgmTy     = ty
                        , tfpgm     = fpgm
                        , teval     = me
                        , ths       = Nothing
                        , tml       = Nothing
                        , trkt      = Nothing
                        , tjs       = Nothing })
     }
  where runIfJust :: Maybe (IO (Maybe a)) -> IO (Maybe a)
        runIfJust Nothing  = return Nothing
        runIfJust (Just i) = i

interp :: Program FlatTerm -> Maybe Int
interp prog =
  case runStd (interpPgm prog) of
    Right (F.FLit i) -> return i
    _ -> Nothing

-- | Different interpreters for the backends
interpHaskell,interpRacket,interpOcaml,interpJS
  :: Program FlatTerm -> IO (Maybe Int)
interpHaskell prog = interpretWith (runBackend hsCompile prog) "runhaskell"
interpRacket  prog = interpretWith (runBackend rktCompile prog) "racket"
interpOcaml   prog = interpretWith (runBackend mlCompile prog) "ocaml"
interpJS      prog = interpretWith (runBackend jsCompile prog) "node"
