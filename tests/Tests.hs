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

allowedErrs :: Int
allowedErrs = 3

main :: IO ()
main =
  do { cases <- mapM testFile =<< getPgmFiles
     ; errs <- concat <$> (mapM (\c -> let err = testCaseErrors c in
                                         if err /= []
                                         then pprint c >> return err
                                         else return err) cases)
     ; let (p,t,f,n,v) = countErrors errs
     ; putStrLn "########### Report ###########"
     ; putStrLn (show (length cases) <+> "test programs")
     ; putStrLn ("Parse errors:             " <+> show p)
     ; putStrLn ("Type errors:              " <+> show t)
     ; putStrLn ("Flattening errors:        " <+> show f)
     ; putStrLn ("Call-by-name eval errors: " <+> show n)
     ; putStrLn ("Call-by-value eval errors:" <+> show v)
     ; exitWith (if length errs - allowedErrs > 0 then ExitFailure 1 else ExitSuccess)
     }

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
    , "type:             " <+> maybe "" pp (tTy test)
    , "expected behavior:" <+> maybe "Undefined" show (tbehavior test)
    , "eval output cbn:  " <+> maybe "" show (tevalCBNOut test)
    , "eval output cbv:  " <+> maybe "" show (tevalCBVOut test)
    , "", ""
    ]

data ErrorType
  = ParseError
  | TypeError
  | FlattenError
  | CBNEvalError
  | CBVEvalError
  deriving (Show,Eq)

instance Pretty ErrorType where
  pp = show

testCaseErrors :: TestCase -> [ErrorType]
testCaseErrors c =
  case tsurface c of
    Nothing -> [ParseError]
    Just _ ->
      case tTy c of
        Nothing ->
          case tbehavior c of
            Just ThrowsTypeError -> []
            _ -> [TypeError]
        Just _ ->
          case tflat c of
            Nothing -> [FlattenError]
            Just _ ->
              case tbehavior c of
                Just (Computes n) ->
                  (case tevalCBNOut c of
                    Just x -> if n == x then [] else [CBNEvalError]
                    Nothing -> [])
                  ++
                  (case tevalCBVOut c of
                    Just x -> if n == x then [] else [CBVEvalError]
                    Nothing -> [])
                _ -> []

countErrors :: [ErrorType] -> (Int,Int,Int,Int,Int)
countErrors = foldr (\err (p,t,f,n,v) ->
                       case err of
                         ParseError -> (p+1,t,f,n,v)
                         TypeError -> (p,t+1,f,n,v)
                         FlattenError -> (p,t,f+1,n,v)
                         CBNEvalError -> (p,t,f,n+1,v)
                         CBVEvalError -> (p,t,f,n,v+1)
                    )
                    (0,0,0,0,0)

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
