{-# LANGUAGE GADTs #-}
module KindSyn where

data Kind where
  KStar :: Kind
  KArr  :: Kind -> Kind -> Kind
