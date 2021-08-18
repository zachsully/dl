{-# LANGUAGE KindSignatures, DataKinds, MultiParamTypeClasses #-}
module DL.General.Strategy where

import DL.Utils.Pretty

data Strategy = CallByName | CallByValue | CallByNeed | CallByLazyValue
  deriving Eq

data StratSingleton :: Strategy -> * where
  SingCBN         :: StratSingleton 'CallByName
  SingCBV         :: StratSingleton 'CallByValue
  SingCBNeed      :: StratSingleton 'CallByNeed
  SingCBLazyValue :: StratSingleton 'CallByLazyValue

instance Eq (StratSingleton s) where
  SingCBN         == SingCBN         = True
  SingCBV         == SingCBV         = True
  SingCBNeed      == SingCBNeed      = True
  SingCBLazyValue == SingCBLazyValue = True

instance Pretty (StratSingleton s) where
  pp SingCBN         = "call-by-name"
  pp SingCBV         = "call-by-value"
  pp SingCBNeed      = "call-by-need"
  pp SingCBLazyValue = "call-by-lazy-value"
