module DL.Pretty where

import Data.Char (toLower)

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
indent lvl s = replicate lvl ' ' <> s

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

quotes :: String -> String
quotes s = "'" <> s <> "'"

parensIf :: (a -> Bool) -> a -> String -> String
parensIf f a s =
  case f a of
    True  -> parens s
    False -> s

brackets :: String -> String
brackets s = "[" <> s <> "]"

bracketsIf :: (a -> Bool) -> a -> String -> String
bracketsIf f a s =
  case f a of
    True  -> brackets s
    False -> s

braces :: String -> String
braces s = "{" <> s <> "}"

pad :: String -> String
pad s = " " <> s <> " "

allLower :: String -> String
allLower = fmap toLower
