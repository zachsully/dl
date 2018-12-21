{-# LANGUAGE GADTs, KindSignatures #-}
module DL.Core.Codata.Syntax where

import DL.General.Type
import DL.General.Variable
import DL.Flat.Syntax

data LCodata :: * where
  CLet :: Variable -> LCodata -> LCodata -> LCodata
  CVar :: Variable -> LCodata
  CFix :: Variable -> LCodata -> LCodata
  CAnn :: LCodata -> Type -> LCodata

  CLit :: Int -> LCodata -- ^ LCodata's single data type
  CAdd :: LCodata -> LCodata -> LCodata

  CCocase :: FlatObsCtx -> LCodata
  CFun    :: Variable -> LCodata -> LCodata
  CCoalt  :: (Variable,LCodata) -> LCodata
  CShift  :: Variable -> LCodata -> LCodata
  CEmpty  :: LCodata
  CPrompt :: LCodata -> LCodata
