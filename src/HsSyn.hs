{-# LANGUAGE GADTs #-}
module HsSyn where

import Data.Monoid

import Utils

data Program
  = Pgm
  { pgmDecls :: [DataTyCons]
  , pgmTerm  :: Term }
  deriving (Show,Eq)

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------
{- Most of the type level is the same as in DualSyn. The notable difference is
   that all of the types are positive so there is no polarity in the data
   declaration.
-}

data Type where
  TyInt  :: Type
  TyArr  :: Type -> Type -> Type
  TyVar  :: TyVariable -> Type
  TyCons :: TyVariable -> Type
  TyApp  :: Type -> Type -> Type
  deriving (Eq,Show)

type TyVariable = String

data DataTyCons
  = DataTyCons
  { dataName  :: TyVariable
  , dataFVars :: [TyVariable]
  , dataCons  :: [DataCon] }
  deriving (Eq,Show)

data DataCon
  = DataCon
  { conName :: Variable
  , conType :: Type }
  deriving (Eq,Show)


--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------
{- This is mostly the same as DualSyn. A lambda term has been introduced to be
   used as an application. The destructor and cocase terms are not present. The
   `fix` term is actually a let
-}

data Term where
  Let  :: Variable -> Term -> Term -> Term
  Lit  :: Int -> Term
  Add  :: Term -> Term -> Term
  Var  :: Variable -> Term
  Lam  :: Variable -> Term -> Term
  App  :: Term -> Term -> Term
  Cons :: Variable -> Term
  Case :: Term -> [(Pattern,Term)] -> Term
  Fail :: Term
  deriving (Eq,Show)

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term]) -> Term
distributeArgs (k,ts) = foldl App (Cons k) ts


{- Only need flat patterns here -}
data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Variable -> [Variable] -> Pattern
  deriving (Eq,Show)

type Variable = String

--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------

ppProgram :: Program -> String
ppProgram pgm = "{-# LANGUAGE GADTs #-}\n"
            <-> (vmconcat (map ppDecl . pgmDecls $ pgm))
            <-> ("\nmain = print $")
            <-> indent 1 ((\t -> ppTerm t 1 9) . pgmTerm $ pgm)

ppDecl :: DataTyCons -> String
ppDecl tc =
  (smconcat ["data",dataName tc,smconcat . dataFVars $ tc,"where"])
  <-> (vmconcat . fmap ppDataCon . dataCons $ tc)
  <-> (indent 1 "deriving Show")
  <> "\n"

ppDataCon :: DataCon -> String
ppDataCon dc =
  indent 1 (conName dc <+> "::" <+> flip ppType 9 . conType $ dc)

ppType :: Type -> Int -> String
ppType TyInt       _ = "Int"
ppType (TyArr a b) p = ppPrec 1 p (ppType a p <+> "->" <+> ppType b p)
ppType (TyVar s)   _ = s
ppType (TyCons s)  _ = s
ppType (TyApp a b) p = ppPrec 9 p (ppType a p <+> ppType b p)

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p = (smconcat ["let",s,"=",ppTerm a (i+2) p])
                           <-> (indent i ("in" <+> (ppTerm b (i+1) p)))
ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = s
ppTerm (Lam s t)     i p = parens ( "\\" <> s <+> "->"
                                  <-> indent (i+2) (ppTerm t (i+3) p))
ppTerm (App a b)     i p = parens (ppTerm a i 9 <+> ppTerm b i p)
ppTerm (Cons s)      _ _ = s
ppTerm (Case t alts) i p =
  "case" <+> ppTerm t i 0 <+> "of"
    <-> (vmconcat . map (indent i . ppAlt) $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (pat,t') = ppPattern pat
                         <+> "->"
                         <-> indent (i+1) (ppTerm t' (i+2) p)

        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar s) = s
        ppPattern (PCons s vs) = s <+> smconcat vs
ppTerm Fail _ _ = "error \"match fail\""
