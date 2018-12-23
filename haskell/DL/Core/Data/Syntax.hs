{-# LANGUAGE GADTs,KindSignatures #-}
module DL.Core.Data.Syntax where

import DL.General.Variable
import DL.General.Type
import DL.Flat.Syntax
import DL.Utils.Pretty

data LData :: * where
  DLet       :: Variable -> LData -> LData -> LData
  DFix       :: Variable -> LData -> LData
  DVar       :: Variable -> LData

  DFun       :: Variable -> LData -> LData    -- ^ The one codata type
  DApp       :: LData -> LData -> LData

  DAnn       :: LData -> Type -> LData
  DLit       :: Int -> LData
  DAdd       :: LData -> LData -> LData
  DConsApp   :: Variable -> [LData] -> LData
  DCase      :: LData
             -> (FlatPattern,LData)
             -> (Variable,LData)
             -> LData
  DCaseEmpty :: LData -> LData

instance Pretty LData where
  ppInd i (DLet s a b)
    = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
      <-> indent i ("in" <+> ppInd (i+3) b)
  ppInd i (DFix s t)
    = "fix" <+> pp s <+> "in"
      <-> indent (i+5) (ppInd (i+5) t)
  ppInd _ (DVar s) = pp s

  ppInd i (DFun v t)
    = "{ λ" <+> ppInd i v <+> "->"
      <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd i (DApp a b)
    = (ppAtomicInd i a) <+> (ppAtomicInd i b)

  ppInd _ (DAnn t ty) = pp t <+> ":" <+> pp ty
  ppInd _ (DLit i) = show i
  ppInd i (DAdd a b)
    = (ppAtomicInd i a) <+> "+" <+> (ppAtomicInd i b)
  ppInd _ (DConsApp k []) = pp k
  ppInd i (DConsApp k vs@(_:_)) = pp k <+> smconcat . fmap (ppInd (i+1)) $ vs
  ppInd i (DCase t (p,u) (y,d))
    = ("case" <+> ppAtomicInd (i+6) t)
      <-> (indent (i+2) "{" <+> pp p <+> "->"
            <+> (ppInd (i+4) u))
      <-> (indent (i+2) "|" <+> pp y <+> "->"
            <+> (ppInd (i+4) d))
      <-> (indent (i+2) "}")
  ppInd i (DCaseEmpty t) = "case" <+> ppInd (i+5) t <+> "{}"

instance Atomic LData where
  isAtomic (DLet _ _ _) = False
  isAtomic (DFix _ _) = False
  isAtomic (DVar _) = True

  isAtomic (DFun _ _) = True
  isAtomic (DApp _ _) = False

  isAtomic (DAnn _ _) = False
  isAtomic (DLit _) = True
  isAtomic (DAdd _ _) = False
  isAtomic (DConsApp _ []) = True
  isAtomic (DConsApp _ (_:_)) = False
  isAtomic (DCase _ _ _) = False
  isAtomic (DCaseEmpty _) = False
