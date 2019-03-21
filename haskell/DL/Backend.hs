{-# LANGUAGE ExistentialQuantification #-}
module DL.Backend (Backend (..),runBackend) where

import DL.General.Top
import DL.Utils.Pretty

-- | A Backend is an object that can compile some type of syntax into a
-- string for output
data Backend syn
  = forall rep. (Pretty rep) => Backend (Program syn -> rep)

runBackend :: Backend syn -> Program syn -> String
runBackend (Backend compile) p = pp (compile p)
