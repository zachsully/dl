{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Control.Monad
import Data.Monoid
import System.FilePath
import System.Directory
import System.Exit
import Text.Read

import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Flat
import DL.Evaluation.Interpreter
import DL.Typecheck
import DL.Utils
import DL.IO
import DL.Pretty
import DL.Translation
import qualified DL.Syntax.Flat               as F
import qualified DL.Syntax.Type               as Ty
import qualified DL.Backend.JavaScript.Syntax as JS
import qualified DL.Backend.Haskell.Syntax    as H
import qualified DL.Backend.ML.Syntax         as ML
import qualified DL.Backend.Racket.Syntax     as Rkt

-- | Holds information for a particular test
data TestCase
  = TestCase
  { tfile   :: FilePath
    -- | Expected output, if available. For now tests must output ints
  , toutput :: Maybe Int
    -- | Parser output
  , tpgm    :: Maybe (Program Term)
    -- | Type checker output
  , pgmTy   :: Maybe Ty.Type
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

instance Pretty TestCase where
  pp (TestCase
      { tfile   = f
      , toutput = o
      , tpgm    = p
      , pgmTy   = t
      , tfpgm   = p'
      , teval   = e
      , ths     = h
      , tml     = m
      , trkt    = r
      , tjs     = j })
    = vmconcat
    [ "===============" <+> f <+> "==============="
    , "did parse?      " <+> (case p of
                          Nothing -> "false"
                          Just _ -> "true"
                       )
    , "type?           " <+> ppMaybe t
    , "expected output?" <+> (case o of
                                Nothing -> "none"
                                Just n -> "some" <> DL.Pretty.parens (show n)
                             )
    , "eval output?    " <+> (case e of
                            Nothing -> "none"
                            Just n -> "some" <> DL.Pretty.parens (show n)
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
                                        Nothing -> a + 1
                                        Just _ -> a
                                   ) 0 cases
              badOutput = foldr (\c a ->
                                      case (do { _ <- tpgm c
                                               ; expected <- toutput c
                                               ; actual <- teval c
                                               ; return (expected == actual) }) of
                                        Nothing -> a
                                        Just True -> a
                                        Just False -> a + 1
                                   ) 0 cases
          in do { putStrLn ("Failed to type:" <+> show failedToType <> "/" <> show n)
                ; putStrLn ("Bad output:" <+> show badOutput <> "/" <> show n)
                ; case (failedToType == 0 && badOutput == 0) of
                    True -> exitWith ExitSuccess
                    False -> exitWith (ExitFailure 42)
                }

getPgmFiles :: IO [FilePath]
getPgmFiles = (fmap ("examples/source/"++) . filter ((==".dl") . takeExtension))
          <$> listDirectory "examples/source"

testFile :: FilePath -> IO TestCase
testFile fp =
  do { mpgm <- getProgram' fp
     ; mout <- getProgramOutput fp
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
     -- ; mhs <- runIfJust (fmap interpHaskell fpgm)
     -- ; mml <- runIfJust (fmap interpOcaml fpgm)
     -- ; mrkt <- runIfJust (fmap interpRacket fpgm)
     ; return (TestCase { tfile   = fp
                        , toutput = mout
                        , tpgm    = mpgm
                        , pgmTy   = ty
                        , tfpgm   = fpgm
                        , teval   = me
                        , ths     = Nothing
                        , tml     = Nothing
                        , trkt    = Nothing
                        , tjs     = Nothing })
     }
  where runIfJust :: Maybe (IO (Maybe a)) -> IO (Maybe a)
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

interp :: Program FlatTerm -> Maybe Int
interp prog =
  case runStd (interpPgm prog) of
    Right (F.FLit i) -> return i
    _ -> Nothing


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
