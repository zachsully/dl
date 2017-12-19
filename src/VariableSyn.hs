module VariableSyn where

import Data.Monoid
import Data.Set

import Pretty

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

instance Monoid Variable where
  mempty = Variable mempty
  mappend (Variable a) (Variable b) = Variable (a <> b)
