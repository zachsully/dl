{-# LANGUAGE GADTs,KindSignatures #-}
module DL.Core.Data.Syntax where

import DL.General.Variable
import DL.General.Type
import DL.Flat.Syntax

data LData :: * where
  DLet       :: Variable -> LData -> LData -> LData
  DVar       :: Variable -> LData

  DFun       :: Variable -> LData -> LData    -- ^ The one codata type
  DApp       :: LData -> LData -> LData

  DFix       :: Variable -> LData -> LData
  DAnn       :: LData -> Type -> LData
  DLit       :: Int -> LData
  DAdd       :: LData -> LData -> LData
  DConsApp   :: Variable -> [LData] -> LData
  DCase      :: LData
             -> (FlatPattern,LData)
             -> (Variable,LData)
             -> LData
  DCaseEmpty :: LData -> LData
