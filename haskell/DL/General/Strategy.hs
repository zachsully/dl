{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses #-}
module DL.General.Strategy where

import DL.Utils.Pretty

data Strategy = CallByName | CallByValue
  deriving Eq

data StratSingleton :: Strategy -> * where
  SingCBN :: StratSingleton 'CallByName
  SingCBV :: StratSingleton 'CallByValue

instance Eq (StratSingleton s) where
  SingCBN == SingCBN = True
  SingCBV == SingCBV = True

instance Pretty (StratSingleton s) where
  pp SingCBN = "call-by-name"
  pp SingCBV = "call-by-value"
