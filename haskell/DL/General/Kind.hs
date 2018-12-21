{-# LANGUAGE GADTs #-}
module DL.General.Kind where

data Kind where
  KStar :: Kind
  KArr  :: Kind -> Kind -> Kind
