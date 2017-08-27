{-# LANGUAGE GADTs #-}
module HsSyn where

import Data.Monoid

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
  Lit  :: Int -> Term
  Add  :: Term -> Term -> Term
  Var  :: Variable -> Term
  Fix  :: Variable -> Term -> Term
  Lam  :: Variable -> Term -> Term
  App  :: Term -> Term -> Term
  Cons :: Variable -> Term
  Case :: Term -> [(Pattern,Term)] -> Term
  deriving (Eq,Show)

data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Variable -> [Pattern] -> Pattern
  deriving (Eq,Show)

type Variable = String

--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------

infixr 0 <+>
(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

infixr 1 <->
(<->) :: String -> String -> String
a <-> b = a <> "\n" <> b

{- concatenates terms with a space between them -}
smconcat :: [String] -> String
smconcat = foldr (<+>) mempty

{- concatenates terms with a newline between them -}
vmconcat :: [String] -> String
vmconcat = foldr (\a b -> a <> "\n" <> b) mempty

parens :: String -> String
parens s = "(" <> s <> ")"

ppProgram :: Program -> String
ppProgram pgm = "{-# LANGUAGE GADTs #-}"
            <-> (vmconcat (map ppDecl . pgmDecls $ pgm))
            <-> ("main = print" <+> (parens . ppTerm . pgmTerm $ pgm))

ppDecl :: DataTyCons -> String
ppDecl tc =
  (smconcat ["data",dataName tc,smconcat . dataFVars $ tc,"where"])
  <-> (vmconcat . fmap ppDataCon . dataCons $ tc)

ppDataCon :: DataCon -> String
ppDataCon dc =
  "  " <> conName dc <+> "::" <+> ppType . conType $ dc

ppType :: Type -> String
ppType TyInt = "Int"
ppType (TyArr a b) = "(" <> ppType a <+> "->" <+> ppType b <> ")"
ppType (TyVar s) = s
ppType (TyCons s) = s
ppType (TyApp a b) = "(" <> ppType a <+> ppType b <> ")"


ppTerm :: Term -> String
ppTerm (Lit i) = show i
ppTerm (Add a b) = "(" <> ppTerm a <+> "+" <+> ppTerm b <> ")"
ppTerm (Var s) = s
ppTerm (Fix s t) = smconcat ["let",s,"=",ppTerm t,"in",s]
ppTerm (Lam s t) = smconcat ["\\",s,"->",ppTerm t]
ppTerm (App a b) = smconcat ["(",ppTerm a,")",ppTerm b]
ppTerm (Cons s) = s
ppTerm (Case t alts) =
  "case" <+> ppTerm t <+> "of"
    <-> (vmconcat . map ppAlt $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (p,t') = ppPattern p <+> "->" <+> ppTerm t'

        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar s) = s
        ppPattern (PCons s ps) =
          s <+> (smconcat . map (\p -> "(" <> ppPattern p <> ")") $ ps)
