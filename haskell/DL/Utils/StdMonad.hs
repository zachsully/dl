module DL.Utils.StdMonad where

import Control.Monad
import Data.Set
import Prelude hiding (log)

import DL.General.Variable
import DL.Utils.Pretty

foldrWithIndex :: (Int -> a -> b -> b) -> b -> [a] -> b
foldrWithIndex f b = snd . Prelude.foldr (\a (i,x) -> (i+1,f i a x)) (0,b)

foldlWithIndex :: (Int -> b -> a -> b) -> b -> [a] -> b
foldlWithIndex f b = snd . Prelude.foldl (\(i,x) a -> (i+1,f i x a)) (0,b)

--------------------------------------------------------------------------------
--                             α-equiv Typeclass                              --
--------------------------------------------------------------------------------

class EqAlpha a where
  eqAlpha :: a -> a -> Bool

--------------------------------------------------------------------------------
--                               Standard Monad                               --
--------------------------------------------------------------------------------
{- This is a monad that can fail and that has a state of unique names. These two
side effects are needed a lot in this code -}

data Std a :: * where
  MkStd :: (StdState -> StdResult a) -> Std a

data StdState :: * where
  StdState :: [String] -- ^ A list of unique names
           -> [String] -- ^ A list of log messages
           -> StdState

data StdResult a :: * where
  StdError  :: [String] -- ^ A list of log messages
            -> String   -- ^ An error message
            -> StdResult a

  StdResult :: [String] -- ^ The rest of the unique names
            -> [String] -- ^ A list of log messages
            -> a        -- ^ The computation result
            -> StdResult a

names :: [String]
names = names' (0 :: Int)
  where names' x = show x : names' (x+1)

runStd :: Std a -> Either String a
runStd (MkStd f) =
  case f (StdState names []) of
    StdError _ err -> Left err
    StdResult _ _ v -> Right v

runStdWithLog :: Std a -> ([String],Either String a)
runStdWithLog (MkStd f) =
  case f (StdState names []) of
    StdError log err -> (reverse log,Left err)
    StdResult _ log v -> (reverse log,Right v)

failure :: String -> Std a
failure s = MkStd $ \(StdState _ log) -> StdError log s

logStd :: String -> Std ()
logStd l = MkStd $ \(StdState ns log) -> StdResult ns (l:log) ()

unimplementedErr :: String -> Std a
unimplementedErr = failure . (mkRed "<unimplemented>" <+>)

typeErr :: String -> Std a
typeErr = failure . (mkRed "<type error>" <+>)

unboundErr :: String -> Std a
unboundErr = failure . (mkRed "<unbound variable>" <+>)

lookupStd :: (Eq a, Pretty a) => a -> [(a,b)] -> Std b
lookupStd a [] = failure (mkRed "<unbound variable>" <+> pp a)
lookupStd a ((x,v):xs) =
  case x == a of
    True  -> return v
    False -> lookupStd a xs

freshVariable :: Std Variable
freshVariable
  = MkStd $ \(StdState (n:ns) log) -> StdResult ns log (Variable ("n" ++ n))

freshen :: Variable -> Std Variable
freshen (Variable v)
  = MkStd $ \(StdState (n:ns) log) -> StdResult ns log (Variable (v ++ n))

instance Functor Std where
  fmap f (MkStd g) = MkStd $ \(StdState ns log) ->
    case g (StdState ns log) of
      StdError log' err -> StdError log' err
      StdResult ns' log' a -> StdResult ns' log' (f a)

instance Applicative Std where
  pure  = return
  (<*>) = ap

instance Monad Std where
  return x = MkStd $ \(StdState ns log) -> StdResult ns log x
  (MkStd f) >>= k =
    MkStd $ \(StdState ns log) ->
      case f (StdState ns log) of
        StdError log' err -> StdError log' err
        StdResult ns' log' a ->
          case k a of MkStd f' -> f' (StdState ns' log')


--------------------------------------------------------------------------------
--                          Free Variable Typeclass                           --
--------------------------------------------------------------------------------

class FV a where
  fvs   :: a → Set Variable
