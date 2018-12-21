module DL.Utils.FreeVars where

import Data.Set
import DL.General.Variable

--------------------------------------------------------------------------------
--                          Free Variable Typeclass                           --
--------------------------------------------------------------------------------

class FV a where
  fvs :: a -> Set Variable
