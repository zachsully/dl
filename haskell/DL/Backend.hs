{-# LANGUAGE ExistentialQuantification #-}
module DL.Backend (Backend (..),runBackend) where

import DL.General.Top
import DL.Flat.Syntax
import DL.Utils.Pretty

-- | A Backend is an object for which we can apply on operation turning a
-- FlatTerm into a String
data Backend = forall rep. (Pretty rep) => Backend (Program FlatTerm -> rep)

runBackend :: Backend -> Program FlatTerm -> String
runBackend (Backend compile) p = pp (compile p)
