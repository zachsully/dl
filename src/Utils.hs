module Utils where

import Data.Monoid
import Control.Monad

--------------------------------------------------------------------------------
--                                  Pretty                                    --
--------------------------------------------------------------------------------
{- A class for pretty printing -}
class Pretty a where
  {-# MINIMAL ppInd | pp #-}
  pp :: a -> String
  pp = ppInd 0

  ppInd :: Int -> a -> String
  ppInd = const pp

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . pp

infixr 0 <+>
(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

infixr 1 <->
(<->) :: String -> String -> String
a <-> b = a <> "\n" <> b

indent :: Int -> String -> String
indent lvl s = replicate (lvl*2) ' ' <> s

stringmconcat :: String -> [String] -> String
stringmconcat _ []     = []
stringmconcat _ (x:[]) = x
stringmconcat s (x:xs) = x <> s <> stringmconcat s xs

{- concatenates terms with a space between them -}
smconcat :: [String] -> String
smconcat = stringmconcat " "

{- concatenates terms with a newline between them -}
vmconcat :: [String] -> String
vmconcat = stringmconcat "\n"

ppPrec :: Int -> Int -> String -> String
ppPrec p p' s = case p > p' of
                  True -> parens s
                  False -> s

parens :: String -> String
parens s = "(" <> s <> ")"

--------------------------------------------------------------------------------
--                               Standard Monad                               --
--------------------------------------------------------------------------------
{- This is a monad that can fail and that has a state of unique names. These two
side effects are needed a lot in this code -}

data Std a = Std { apStd :: [String] -> Either String (a,[String]) }

names :: [String]
names = names' (0 :: Int)
  where names' x = ("x" ++ show x) : names' (x+1)

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
lookupStd a [] = failure ("<unbound>" <+> pp a)
lookupStd a ((x,v):xs) =
  case x == a of
    True  -> return v
    False -> lookupStd a xs

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
