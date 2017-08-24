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
   used as an application. The destructor and cocase terms are not present. The
   `fix` term is actually a let
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
ppProgram (Program decls term) = "{-# LANGUAGE GADTs #-}"
                             <-> (vmconcat (map ppDecl decls))
                             <-> ("main = print" <+> parens (ppTerm term))

ppDecl :: Decl -> String
ppDecl (Decl s fts ds) =
  (smconcat ["data",ppTySymbol s,smconcat . fmap ppTyVariable $ fts,"where"])
  <-> (vmconcat . fmap ppData $ ds)

ppData :: Data -> String
ppData (Data (Symbol s) typ) =
  "  " <> s <+> "::" <+> ppType typ

ppType :: Type -> String
ppType TyInt = "Int"
ppType (TyArr a b) = "(" <> ppType a <+> "->" <+> ppType b <> ")"
ppType (TyVar v) = ppTyVariable v
ppType (TyCons s tys) = "(" <> ppTySymbol s <+> (smconcat . fmap ppType $ tys)
                      <> ")"

ppTyVariable :: TyVariable -> String
ppTyVariable (TyVariable s) = s

ppTySymbol :: TySymbol -> String
ppTySymbol (TySymbol s) = s


ppTerm :: Term -> String
ppTerm (Lit i) = show i
ppTerm (Add a b) = "(" <> ppTerm a <+> "+" <+> ppTerm b <> ")"
ppTerm (Var (Variable s)) = s
ppTerm (Fix (Variable s) t) = smconcat ["let",s,"=",ppTerm t,"in",s]
ppTerm (Lam (Variable s) t) = smconcat ["\\",s,"->",ppTerm t]
ppTerm (App a b) = smconcat ["(",ppTerm a,")",ppTerm b]
ppTerm (Cons (Symbol s) ts) =
  s <+> (smconcat . map (\t -> "(" <> ppTerm t <> ")") $ ts)
ppTerm (Case t alts) =
  "case" <+> ppTerm t <+> "of"
    <-> (vmconcat . map ppAlt $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (p,t) = ppPattern p <+> "->" <+> ppTerm t

        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar (Variable s)) = s
        ppPattern (PCons (Symbol s) ps) =
          s <+> (smconcat . map (\p -> "(" <> ppPattern p <> ")") $ ps)
