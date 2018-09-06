module DL.Utils where

import Control.Monad
import Data.Set

import DL.Syntax.Variable
import DL.Pretty

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

data Std a = Std { apStd :: [String] -> Either String (a,[String]) }

names :: [String]
names = names' (0 :: Int)
  where names' x = show x : names' (x+1)

runStd :: Std a -> Either String a
runStd m =
  case apStd m names of
    Left s -> Left s
    Right (a,_) -> Right a

failure :: String -> Std a
failure s = Std $ \_ -> Left s

unimplementedErr :: String -> Std a
unimplementedErr = failure . ("<unimplemented>" <+>)

typeErr :: String -> Std a
typeErr = failure . ("<type error>" <+>)

unboundErr :: String -> Std a
unboundErr = failure . ("<unbound variable>" <+>)

lookupStd :: (Eq a, Pretty a) => a -> [(a,b)] -> Std b
lookupStd a [] = failure ("<unbound variable>" <+> pp a)
lookupStd a ((x,v):xs) =
  case x == a of
    True  -> return v
    False -> lookupStd a xs

freshVariable :: Std Variable
freshVariable = Std $ \(n:ns) -> Right (Variable ("n" ++ n),ns)

freshen :: Variable -> Std Variable
freshen (Variable v) = Std $ \(n:ns) -> Right (Variable (v ++ n),ns)

instance Functor Std where
  fmap f m = Std $ \ns ->
    case apStd m ns of
      Left s -> Left s
      Right (a,ns') -> Right (f a, ns')

instance Applicative Std where
  pure  = return
  (<*>) = ap

instance Monad Std where
  return x = Std $ \ns -> Right (x,ns)
  m >>= f =
    Std $ \ns ->
      case apStd m ns of
        Left s -> Left s
        Right (a,ns') -> apStd (f a) ns'


--------------------------------------------------------------------------------
--                          Free Variable Typeclass                           --
--------------------------------------------------------------------------------

class FV a where
  fvs   :: a → Set Variable
