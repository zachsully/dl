module Utils where

import Data.Monoid

infixr 0 <+>
(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

infixr 1 <->
(<->) :: String -> String -> String
a <-> b = a <> "\n" <> b

indent :: Int -> String -> String
indent lvl s = replicate (lvl*2) ' ' <> s

{- concatenates terms with a space between them -}
smconcat :: [String] -> String
smconcat []     = []
smconcat (x:[]) = x
smconcat (x:xs) = x <+> smconcat xs

{- concatenates terms with a newline between them -}
vmconcat :: [String] -> String
vmconcat []     = []
vmconcat (x:[]) = x
vmconcat (x:xs) = x <-> vmconcat xs

ppPrec :: Int -> Int -> String -> String
ppPrec p p' s = case p > p' of
                  True -> parens s
                  False -> s

parens :: String -> String
parens s = "(" <> s <> ")"
