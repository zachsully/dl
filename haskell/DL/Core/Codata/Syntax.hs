{-# LANGUAGE GADTs, KindSignatures #-}
module DL.Core.Codata.Syntax where

import DL.General.Type
import DL.General.Variable

data LCodata :: * where
  CLet :: Variable -> LCodata -> LCodata -> LCodata
  CVar :: Variable -> LCodata
  CFix :: Variable -> LCodata -> LCodata
  CAnn :: LCodata -> Type -> LCodata

  CLit :: Int -> LCodata -- ^ LCodata's single data type
  CAdd :: LCodata -> LCodata -> LCodata

  CFun    :: Variable -> LCodata -> LCodata
  CCoalt  :: (Variable,LCodata) -> LCodata
  CShift  :: Variable -> LCodata -> LCodata
  CEmpty  :: LCodata
  CPrompt :: LCodata -> LCodata

  CObsApp  :: LCodata -> LCodata -> LCodata
  CObsDest :: Variable -> LCodata -> LCodata
  CObsCut  :: Variable -> LCodata -> LCodata
