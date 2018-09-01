{-# LANGUAGE GADTs #-}
module DL.Backend.Haskell.Syntax where

import qualified DL.Syntax.Type as Ty
import qualified DL.Syntax.Top  as Top
import DL.Syntax.Flat
import DL.Translation
import DL.Syntax.Variable
import DL.Pretty

data Program
  = Pgm
  { pgmTyDecls  :: [Either DataTyCons RecordTyCons]
  , pgmFunDecls :: [FunDecl]
  , pgmTerm     :: Term }
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

data FunDecl
  = FunDecl
  { funName :: Variable
  , funArgs :: [Variable]
  , funRhs  :: Term }
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

instance Pretty Program where
  pp pgm =   "{-# LANGUAGE GADTs #-}"
         <-> "module Main where"
         <-> ""
         <-> "import Prelude (Show, IO, error, print, (+))"
         <-> ""
         <-> (vmconcat . fmap ppTyDecl . pgmTyDecls $ pgm)
         <-> ""
         <-> (vmconcat . fmap pp . pgmFunDecls $ pgm)
         <-> ""
         <-> "prog =" <-> indent 1 ((\t -> ppTerm t 1 9) . pgmTerm $ pgm)
         <-> ""
         <-> "main :: IO ()\nmain = print prog"

ppTyDecl :: Either DataTyCons RecordTyCons -> String
ppTyDecl = either ppDataDecl ppRecordDecl

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


instance Pretty FunDecl where
  pp fd =   (unVariable . funName $ fd)
        <+> (smconcat . fmap (allLower . unVariable) . funArgs $ fd)
        <+> "="
        <-> indent 1 (ppTerm (funRhs fd) 1 9)

ppType :: Type -> Int -> String
ppType TyInt       _ = "Int"
ppType (TyArr a b) p = ppPrec 1 p (ppType a p <+> "->" <+> ppType b p)
ppType (TyVar s)   _ = pp s
ppType (TyCons s)  _ = pp s
ppType (TyApp a b) p = ppPrec 9 p (ppType a p <+> ppType b p)

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p =     (smconcat ["let {",pp s,"="])
                           <-> indent (i+1) (ppTerm a (i+1) p) <+> "}"
                           <-> indent i "in"
                           <-> indent (i+1) (ppTerm b (i+1) p)
ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = pp s
ppTerm (Lam s t)     i p = parens ( "\\" <> pp s <+> "->" <+> (ppTerm t (i+3) p))
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

--------------------------------------------------------------------------------
--                              Translation                                   --
--------------------------------------------------------------------------------

instance Translate Program where
  translate = trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: Top.Program FlatTerm -> Program
trans dpgm =
  let (decls',fds) = foldr (\d (ds,fs) ->
                              let (d',fs') = transDecl d
                              in  (d':ds,fs'<>fs))
                           ([],[])
                           (Top.pgmDecls dpgm)
  in Pgm decls' fds (transTerm . Top.pgmTerm $ dpgm)

transType :: Ty.Type -> Type
transType Ty.TyInt       = TyInt
transType (Ty.TyArr a b) = TyArr (transType a) (transType b)
transType (Ty.TyApp a b) = TyApp (transType a) (transType b)
transType (Ty.TyVar v)   = TyVar v
transType (Ty.TyCons k)  = TyCons k

typeCodom :: Type -> Type
typeCodom (TyArr _ b) = b
typeCodom x = error ("type" <+> ppType x 0 <+> "is not a projection")

transDecl
  :: Top.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl (Top.Decl (Right d)) =
  (Left (DataTyCons
          (Top.posTyName d)
          (Top.posTyFVars d)
          (fmap mkDataCon . Top.injections $ d))
  , [] )
  where mkDataCon :: Top.Injection -> DataCon
        mkDataCon inj = DataCon (Top.injName inj)
                                   (transType . Top.injType $ inj)

transDecl (Top.Decl (Left d))  =
  ( Right (RecordTyCons
           name
           (Top.negTyFVars d)
           (fmap mkRecordField (Top.projections d)))
  , fmap setter . Top.projections $ d )
  where name = Top.negTyName d
        pname p = Variable "_" <> Top.projName p

        setter :: Top.Projection -> FunDecl
        setter p = FunDecl
          { funName = Variable "set_" <> Top.projName p
          , funArgs = [Variable "cd", Variable "br"]
          , funRhs  =
              foldl (\c p' ->
                        let t = case p == p' of
                                  True  -> Var (Variable "br")
                                  False -> App (Var (pname p')) (Var (Variable "cd"))
                        in App c t
                    )
                    (Cons name)
                    (Top.projections d)
          }

        mkRecordField :: Top.Projection -> Field
        mkRecordField p = Field (pname p)
                                   (typeCodom . transType . Top.projType $ p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FFix v a) = let a' = transTerm a in Let v a' a'
transTerm (FVar v) = Var v

transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)

transTerm (FConsApp v fts) = foldr App (Var v) . fmap transTerm $ fts
transTerm (FCase t (p,u) (y,d)) = Case (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(PVar y,transTerm d)]
transTerm (FCaseEmpty t) = App (Var (Variable "(error \"unmatched\")")) (transTerm t)

transTerm (FCoalt (h,u) t) = App (App (Var (Variable "set_" <> h))
                                      (transTerm t))
                                 (transTerm u)
transTerm (FEmpty) = Fail
transTerm (FFun v t) = Lam v (transTerm t)
transTerm (FCocase (FlatObsFun e) t) = App (transTerm t) (transTerm e)
transTerm (FCocase (FlatObsDest h) t) = App (Var (Variable "_" <> h))
                                            (transTerm t)

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs
