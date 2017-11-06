{-# LANGUAGE GADTs #-}
module Syntax.Typed.Kind where

data Kind where
  KStar :: Kind
  KArr  :: Kind -> Kind -> Kind
