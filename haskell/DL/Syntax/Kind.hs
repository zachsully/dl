{-# LANGUAGE GADTs #-}
module DL.Syntax.Kind where

data Kind where
  KStar :: Kind
  KArr  :: Kind -> Kind -> Kind
