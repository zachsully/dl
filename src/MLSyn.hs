{-# LANGUAGE GADTs #-}
module MLSyn where

import Data.Monoid

import qualified DualSyn as D
import qualified TypeSyn as Ty
import Flatten
import Translation
import VariableSyn
import Pretty
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
declaration. -}

data Type where
  TyInt  :: Type
  TyArr  :: Type -> Type -> Type
  TyVar  :: Variable -> Type
  TyCons :: Variable -> Type
  TyApp  :: Type -> Type -> Type
  TyLazy :: Type -> Type
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
`fix` term is actually a let. For ML we also introduct Lazy and Force. -}

data Term where
  Let   :: Variable -> Term -> Term -> Term
  Lazy  :: Term -> Term
  Force :: Term -> Term
  Lit   :: Int -> Term
  Add   :: Term -> Term -> Term
  Var   :: Variable -> Term
  Lam   :: Variable -> Term -> Term
  App   :: Term -> Term -> Term
  Cons  :: Variable -> Term
  Case  :: Term -> [(Pattern,Term)] -> Term
  Fail  :: Term
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
ppProgram pgm = "open Lazy\n"
            <-> (vmconcat (map ppDecl . pgmDecls $ pgm))
            <-> ("\nlet prog =" <+> ((\t -> ppTerm t 2 9) . pgmTerm $ pgm) <> ";;")
            <-> "\nprint_int prog;;\nprint_newline ();;\n"

ppDecl :: Either DataTyCons RecordTyCons -> String
ppDecl = either ppDataDecl ppRecordDecl

ppDataDecl :: DataTyCons -> String
ppDataDecl tc =
  (smconcat ["type",unVariable . dataName $ tc,smconcat . fmap unVariable . dataFVars $ tc])
  <-> (vmconcat . fmap ppDataCon . dataCons $ tc)
  <> "\n"

ppDataCon :: DataCon -> String
ppDataCon dc =
  indent 1 ((unVariable . conName $ dc) <+> ":" <+> flip ppType 9 . conType $ dc)

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
ppType TyInt       _ = "int"
ppType (TyArr a b) p = ppPrec 1 p (ppType a p <+> "->" <+> ppType b p)
ppType (TyVar s)   _ = unVariable s
ppType (TyCons s)  _ = unVariable s
ppType (TyApp a b) p = ppPrec 9 p (ppType a p <+> ppType b p)
ppType (TyLazy a)  p = parens (ppType a p) <+> "lazy_t"

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p = smconcat ["let",unVariable s,"=",ppTerm a i p,"in"]
                           <-> indent i (ppTerm b i p)
ppTerm (Lazy t)      i p = "lazy" <+> parens (ppTerm t i p)
ppTerm (Force t)     i p = "force" <+> parens (ppTerm t i p)

ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = unVariable s
ppTerm (Lam s t)     i p = parens ( "\\" <> unVariable s <+> "->"
                                  <-> indent i (ppTerm t (i+1) p))
ppTerm (App a b)     i p = parens (ppTerm a i 9 <+> ppTerm b i p)
ppTerm (Cons s)      _ _ = unVariable s
ppTerm Fail          _ _ = "(Error.of_string \"unmatched (co)pattern\")"
ppTerm (Case t alts) i p =
  "case" <+> ppTerm t i 0 <+> "of"
    <-> (vmconcat . map (indent i . ppAlt) $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (pat,t') = ppPattern pat
                         <+> "->"
                         <-> indent (i+1) (ppTerm t' (i+2) p)

        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar s) = unVariable s
        ppPattern (PCons s vs) = (unVariable s) <+> (smconcat . map unVariable $ vs)

--------------------------------------------------------------------------------
--                              Translation                                   --
--------------------------------------------------------------------------------


instance Translate Program where
  translate = trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: D.Program FlatTerm -> Program
trans dpgm =
  let (f,decls') = foldr (\d (f,ds) ->
                           let (df,d') = transDecl d
                           in  (df . f, d':ds) )
                         (id,[])
                         (D.pgmDecls dpgm)
  in Pgm decls' ( f . transTerm . D.pgmTerm $ dpgm )

transType :: Ty.Type -> Type
transType Ty.TyInt       = TyInt
transType (Ty.TyArr a b) = TyArr (transType a) (transType b)
transType (Ty.TyApp a b) = TyApp (transType a) (transType b)
transType (Ty.TyVar v)   = TyVar v
transType (Ty.TyCons k)  = TyCons k

transDecl
  :: D.Decl
  -> (Term -> Term, Either DataTyCons RecordTyCons)
transDecl (Right d) =
  (id, Left (DataTyCons (Ty.posTyName d)
                           (Ty.posTyFVars d)
                           (fmap mkDataCon . Ty.injections $ d)))
  where mkDataCon :: Ty.Injection -> DataCon
        mkDataCon inj = DataCon (Ty.injName inj)
                                   (transType . Ty.injType $ inj)

transDecl (Left d)  =
  ( addSetters (Ty.projections d) 0
  , Right (RecordTyCons name
                           (Ty.negTyFVars d)
                           (fmap mkRecordField (Ty.projections d))))
  where name = Variable "Mk" <> Ty.negTyName d
        pname p = Variable "_" <> Ty.projName p

        numProjs = length . Ty.projections $ d

        -- an association between projections and their index
        pIndexAssoc :: [(Int,Ty.Projection)]
        pIndexAssoc = foldrWithIndex (\i p a -> (i,p):a) [] (Ty.projections d)

        addSetters :: [Ty.Projection] -> Int -> (Term -> Term)
        addSetters [] _ = id
        addSetters (p:ps) i =
          (Let
            setterName
            (Lam (Variable "d")
              (Lam (Variable "x")
                (foldlWithIndex (\j c p ->
                                  let t = case i == j of
                                            True  -> Var (Variable "x")
                                            False -> App (Var (pname p))
                                                            (Var (Variable "d"))
                                  in App c t
                                )
                                (Cons name)
                                (Ty.projections d))))) --App(App (Cons name) (Var "x"))))))
          . (addSetters ps (i+1))
          where setterName = Variable "set_" <> Ty.projName p

        mkRecordField :: Ty.Projection -> Field
        mkRecordField p = Field (pname p)
                                   (transType . Ty.projType $ p)

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
