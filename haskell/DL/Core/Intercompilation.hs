module DL.Core.Intercompilation
  ( visitor
  , tabulate
  ) where

import DL.Core.Data.Syntax
import DL.Core.Codata.Syntax
import DL.Utils.StdMonad

--------------------------------------------------------------------------------
--                               Visitor                                      --
--------------------------------------------------------------------------------
visitor :: LData -> Std LCodata
visitor (DLet v a b)   = CLet v <$> visitor a <*> visitor b
visitor (DFix v a)     = CFix v <$> visitor a
visitor (DVar v)       = pure (CVar v)
visitor (DAnn a ty)    = CAnn <$> visitor a <*> pure ty

-- ^ positive cases
visitor (DLit i)       = pure (CLit i)
visitor (DAdd a b)     = CAdd <$> visitor a <*> visitor b
visitor (DConsApp _ _) = undefined
visitor (DCase _ _ _)  = undefined
visitor (DCaseEmpty _) = undefined

-- ^ negative cases
visitor (DFun v a)     = CFun v <$> visitor a
visitor (DApp a b)     = CObsApp <$> visitor a <*> visitor b

--------------------------------------------------------------------------------
--                              Tabulation                                    --
--------------------------------------------------------------------------------
tabulate :: LCodata -> Std LData
tabulate (CLet v a b)   = DLet v <$> tabulate a <*> tabulate b
tabulate (CFix v a)     = DFix v <$> tabulate a
tabulate (CVar v)       = pure (DVar v)
tabulate (CAnn a ty)    = DAnn <$> tabulate a <*> pure ty

-- ^ positive cases
tabulate (CLit i)       = pure (DLit i)
tabulate (CAdd a b)     = DAdd <$> tabulate a <*> tabulate b

-- ^ negative cases
tabulate (CFun v a)     = DFun v <$> tabulate a
tabulate (CCoalt _ _)   = undefined
tabulate (CShift _ _)   = undefined
tabulate CEmpty         = undefined
tabulate (CPrompt _)    = undefined
tabulate (CObsApp _ _)  = undefined
tabulate (CObsDest _ _) = undefined
tabulate (CObsCut _ _)  = undefined
