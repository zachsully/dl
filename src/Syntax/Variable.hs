module Syntax.Variable where

import Data.Monoid       

{- Vars are introduced and consumed by pattern matching within terms. -}
type Variable = String

varStream :: [Variable]
varStream = fmap (("v" <>) . show) [1..]

class FV a where
  freeVars :: a -> [Variable]

class BV a where
  boundVars :: a -> [Variable]

class Bind a where
  binds :: a -> [Variable]
