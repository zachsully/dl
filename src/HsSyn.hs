{-# LANGUAGE GADTs #-}
module HsSyn where

import Data.Monoid

import VariableSyn
import Utils

data Program
  = Pgm
  { pgmDecls :: [Either DataTyCons RecordTyCons]
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
  TyVar  :: Variable -> Type
  TyCons :: Variable -> Type
  TyApp  :: Type -> Type -> Type
  deriving (Eq,Show)

data DataTyCons
  = DataTyCons
  { dataName  :: Variable
  , dataFVars :: [Variable]
  , dataCons  :: [DataCon] }
  deriving (Eq,Show)

data DataCon
  = DataCon
  { conName :: Variable
  , conType :: Type }
  deriving (Eq,Show)

data RecordTyCons
  = RecordTyCons
  { recordName   :: Variable
  , recordFVars  :: [Variable]
  , recordFields :: [Field] }
  deriving (Eq,Show)

data Field
  = Field
  { fieldName :: Variable
  , fieldType :: Type }
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

--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------

ppProgram :: Program -> String
ppProgram pgm = "{-# LANGUAGE GADTs #-}\n"
            <-> (vmconcat (map ppDecl . pgmDecls $ pgm))
            <-> ("\nmain = print $")
            <-> indent 1 ((\t -> ppTerm t 1 9) . pgmTerm $ pgm)

ppDecl :: Either DataTyCons RecordTyCons -> String
ppDecl = either ppDataDecl ppRecordDecl

ppDataDecl :: DataTyCons -> String
ppDataDecl d = "data"
           <+> pp (dataName d)
           <+> (smconcat . fmap unVariable . dataFVars $ d)
           <+> "where"
           <-> (vmconcat . fmap ppDataCons . dataCons $ d)
           <-> (indent 1 "deriving Show\n")

  where ppDataCons :: DataCon -> String
        ppDataCons dc = indent 1 (   pp (conName dc)
                                 <+> "::"
                                 <+> flip ppType 9 . conType $ dc )


ppRecordDecl :: RecordTyCons -> String
ppRecordDecl r = "data"
             <+> pp (recordName r)
             <+> (smconcat . fmap pp . recordFVars $ r)
             <-> indent 1 "="
             <+> pp (recordName r)
             <-> indent 1 "{" <+> (stringmconcat (indent 1 ", ")
                                   (fmap ppRecordField . recordFields $ r))
             <> indent 1 "} deriving Show"

ppRecordField :: Field -> String
ppRecordField f = pp (fieldName f)
  <+> "::"
  <+> (flip ppType 9 . fieldType $ f) <> "\n"

ppType :: Type -> Int -> String
ppType TyInt       _ = "Int"
ppType (TyArr a b) p = ppPrec 1 p (ppType a p <+> "->" <+> ppType b p)
ppType (TyVar s)   _ = pp s
ppType (TyCons s)  _ = pp s
ppType (TyApp a b) p = ppPrec 9 p (ppType a p <+> ppType b p)

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p = (smconcat ["let",pp s,"="])
                           <+> (ppTerm a (i+1) p)
                           <-> (indent i "in")
                           <+> (ppTerm b (i+1) p)
ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = pp s
ppTerm (Lam s t)     i p = parens ( "\\" <> pp s <+> "->"
                                  <-> indent (i+2) (ppTerm t (i+3) p))
ppTerm (App a b)     i p = ppTerm a i 9 <+> (parens (ppTerm b i p))
ppTerm (Cons s)      _ _ = pp s
ppTerm (Case t alts) i p =
  "case" <+> ppTerm t i 0 <+> "of"
    <-> (vmconcat . map (indent i . ppAlt) $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (pat,t') = ppPattern pat
                         <+> "->"
                         <-> indent (i+1) (ppTerm t' (i+2) p)

        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar s) = pp s
        ppPattern (PCons s vs) = pp s <+> smconcat . fmap pp $ vs
ppTerm Fail _ _ = "(error \"match fail\")"
