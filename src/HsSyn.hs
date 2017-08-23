{-# LANGUAGE GADTs #-}
module HsSyn where

import Data.Monoid

data Program = Program [Decl] Term
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
  TyCons :: TySymbol -> [Type] -> Type
  deriving (Eq,Show)

newtype TySymbol = TySymbol String
  deriving (Eq,Show)

newtype TyVariable = TyVariable String
  deriving (Eq,Show)

data Decl = Decl TySymbol [TyVariable] [Data]
  deriving (Eq,Show)

data Data = Data Symbol Type
  deriving (Eq,Show)


--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------
{- This is mostly the same as DualSyn. A lambda term has been introduced to be
   used as an application. The destructor and cocase terms are not present.
-}

data Term where
  Lit :: Int -> Term
  Add :: Term -> Term -> Term
  Var :: Variable -> Term
  Fix :: Variable -> Term -> Term
  Lam :: Variable -> Term -> Term
  App :: Term -> Term -> Term
  Cons :: Symbol -> [Term] -> Term
  Case :: Term -> [(Pattern,Term)] -> Term
  deriving (Eq,Show)

data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Symbol -> [Pattern] -> Pattern
  deriving (Eq,Show)

newtype Symbol = Symbol String
  deriving (Eq,Show)

newtype Variable = Variable String
  deriving (Eq,Show)

--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------

(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

{- concatenates terms with a space between them -}
smconcat :: [String] -> String
smconcat = foldr (<+>) mempty

{- concatenates terms with a newline between them -}
vmconcat :: [String] -> String
vmconcat = foldr (\a b -> a <> "\n" <> b) mempty

ppProgram :: Program -> String
ppProgram (Program decls term) = vmconcat [vmconcat (map ppDecl decls)
                                          ,ppTerm term]

ppDecl :: Decl -> String
ppDecl = error "ppDecl"

ppType :: Type -> String
ppType = error "ppType"

ppTerm :: Term -> String
ppTerm (Lit i) = show i
ppTerm (Add a b) = "(" <> ppTerm a <+> "+" <+> ppTerm b <> ")"
ppTerm (Var _) = undefined
ppTerm (Fix _ _) = undefined
ppTerm (Lam _ _) = undefined
ppTerm (App _ _) = undefined
ppTerm (Cons _ _) = undefined
ppTerm (Case _ _) = undefined
