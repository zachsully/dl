module VariableSyn where

import Data.Monoid

import Utils

{- Vars are introduced and consumed by pattern matching within terms. -}
newtype Variable = Variable String

unVariable :: Variable -> String
unVariable (Variable s) = s

freshVariable :: Std Variable
freshVariable = Std $ \(n:ns) -> Right (Variable n,ns)

instance Eq Variable where
  a == b = unVariable a == unVariable b

instance Pretty Variable where
  pp = unVariable

instance Show Variable where
  show = unVariable

instance Monoid Variable where
  mempty = Variable mempty
  mappend (Variable a) (Variable b) = Variable (a <> b)
