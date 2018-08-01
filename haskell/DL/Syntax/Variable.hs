module DL.Syntax.Variable where

import qualified Data.Semigroup as S
import qualified Data.Monoid as M
import DL.Pretty

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
    (<>) (Variable a) (Variable b) = Variable (a M.<> b)

instance Monoid Variable where
  mempty = Variable mempty
  mappend = (S.<>)
