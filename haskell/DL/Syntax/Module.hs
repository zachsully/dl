module DL.Syntax.Module where

import Data.Set

data Module = Module { moduleSet :: Set ModuleDecl }

data ModuleDecl
  = CodataDecl NegativeTyCons
  | DataDecl   PositiveTyCons
  | VarDecl    Variable Term
  | CovarDecl  Variable ObsCtx
