{-# LANGUAGE GADTs #-}
module HsSyn where

import Data.Monoid

import qualified DualSyn as D
import qualified TypeSyn as Ty
import Flatten
import Translation
import VariableSyn
import Pretty

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
trans :: D.Program FlatTerm -> Program
trans dpgm =
  let (decls',fds) = foldr (\d (ds,fs) ->
                              let (d',fs') = transDecl d
                              in  (d':ds,fs'<>fs))
                           ([],[])
                           (D.pgmDecls dpgm)
  in Pgm decls' fds (transTerm . D.pgmTerm $ dpgm)

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
  :: D.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl (Right d) =
  (Left (DataTyCons
          (Ty.posTyName d)
          (Ty.posTyFVars d)
          (fmap mkDataCon . Ty.injections $ d))
  , [] )
  where mkDataCon :: Ty.Injection -> DataCon
        mkDataCon inj = DataCon (Ty.injName inj)
                                   (transType . Ty.injType $ inj)

transDecl (Left d)  =
  ( Right (RecordTyCons
           name
           (Ty.negTyFVars d)
           (fmap mkRecordField (Ty.projections d)))
  , fmap setter . Ty.projections $ d )
  where name = Ty.negTyName d
        pname p = Variable "_" <> Ty.projName p

        setter :: Ty.Projection -> FunDecl
        setter p = FunDecl
          { funName = Variable "set_" <> Ty.projName p
          , funArgs = [Variable "cd", Variable "br"]
          , funRhs  =
              foldl (\c p' ->
                        let t = case p == p' of
                                  True  -> Var (Variable "br")
                                  False -> App (Var (pname p')) (Var (Variable "cd"))
                        in App c t
                    )
                    (Cons name)
                    (Ty.projections d)
          }

        mkRecordField :: Ty.Projection -> Field
        mkRecordField p = Field (pname p)
                                   (typeCodom . transType . Ty.projType $ p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)
transTerm (FVar v) = Var v
transTerm (FFix v a) = let a' = transTerm a in Let v a' a'
transTerm (FApp a b) = App (transTerm a) (transTerm b)
transTerm (FCons k) = Cons k
transTerm (FCase t (p,u) d) = Case (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(PWild,transTerm d)]
transTerm (FDest h) = Var (Variable "_" <> h)
transTerm (FCoCase (q,u) d) = transCoalt (q,u) (transTerm d)
transTerm (FFail) = Fail

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs

transCoalt :: (FlatCopattern, FlatTerm) -> Term -> Term
transCoalt (FlatCopDest h,u) t = App (App (Var (Variable "set_" <> h)) t)
                                           (transTerm u)
transCoalt (FlatCopPat _,u) _ = transTerm u
