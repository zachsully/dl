module DL.Core.Codata.Syntax where

import DL.General.Type
import DL.General.Variable
import DL.Utils.Pretty

data LCodata :: * where
  CLet :: Variable -> LCodata -> LCodata -> LCodata
  CVar :: Variable -> LCodata
  CFix :: Variable -> LCodata -> LCodata
  CAnn :: LCodata -> Type -> LCodata

  CLit :: Int -> LCodata
  CAdd :: LCodata -> LCodata -> LCodata

  CFun    :: Variable -> LCodata -> LCodata
  CCoalt  :: (Variable,LCodata) -> LCodata -> LCodata
  CShift  :: Variable -> LCodata -> LCodata
  CEmpty  :: LCodata
  CPrompt :: LCodata -> LCodata

  CObsApp  :: LCodata -> LCodata -> LCodata
  CObsDest :: Variable -> LCodata -> LCodata
  CObsCut  :: Variable -> LCodata -> LCodata

instance Pretty LCodata where
  ppInd _ (CVar s)         = pp s
  ppInd i (CFix s t)       = "fix" <+> pp s <+> "in"
                           <-> indent (i+5) (ppInd (i+5) t)
  ppInd _ (CAnn t ty)      = pp t <+> ":" <+> pp ty
  ppInd i (CLet s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                            <-> indent i ("in" <+> ppInd (i+3) b)

  ppInd _ (CLit i)         = show i
  ppInd i (CAdd a b)       = (ppAtomicInd i a)
                         <+> "+"
                         <+> (ppAtomicInd i b)

  ppInd i (CFun v t)       =  "{ #" <+> ppInd i v <+> "->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd i (CCoalt (h,u) d) = "{" <+> pp h <+> "# ->"
                               <-> indent (i+3) (ppInd (i+3) u)
                          <-> (indent (i+3) "," <+> "_ ->"
                               <+> (ppInd (i+3) d))
                          <-> (indent (i+3) "}")
  ppInd i (CShift v t)     =  "{" <+> ppInd i v <+> "# ->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd _ CEmpty           = "{}"
  ppInd i (CPrompt t)      = "#" <+> ppInd (i+2) t

  ppInd i (CObsApp a b)    =
    "cocase" <-> ("[#" <+> (ppAtomicInd (i+3) a) <> "]")
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (CObsDest h b)    =
    "cocase" <-> (brackets (pp h <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (CObsCut v b)    =
    "cocase" <-> (brackets (pp v <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)

instance Atomic LCodata where
  isAtomic (CLet _ _ _) = False
  isAtomic (CVar _) = True
  isAtomic (CFix _ _) = False
  isAtomic (CAnn _ _) = False

  isAtomic (CLit _) = True
  isAtomic (CAdd _ _) = False

  isAtomic (CFun _ _) = True
  isAtomic (CCoalt _ _) = True
  isAtomic (CShift _ _) = True
  isAtomic CEmpty = True
  isAtomic (CPrompt _) = False

  isAtomic (CObsApp _ _) = False
  isAtomic (CObsDest _ _) = False
  isAtomic (CObsCut _ _) = False

capps :: LCodata -> [LCodata] -> LCodata
capps f [] = f
capps f (a:as) = foldr CObsApp f (a:as)

cfail :: LCodata
cfail = CVar (Variable "failure")
