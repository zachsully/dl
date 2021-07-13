module DL.Syntax.Variable where

import Data.Monoid
import Data.Set

import DL.Pretty

{- Vars are introduced and consumed by pattern matching within terms. -}
newtype Variable = Variable String
  deriving Ord

unVariable :: Variable -> String
unVariable (Variable s) = s

instance Eq Variable where
  a == b = unVariable a == unVariable b

instance Pretty Variable where
  pp = unVariable

instance Show Variable where
  show = unVariable

instance Semigroup Variable where
 (Variable a) <> (Variable b) = Variable (a <> b)

instance Monoid Variable where
  mempty = Variable mempty
