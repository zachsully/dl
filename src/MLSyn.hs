{-# LANGUAGE GADTs #-}
module MLSyn where

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
declaration. -}

data Type where
  TyInt  :: Type
  TyArr  :: Type -> Type -> Type
  TyVar  :: Variable -> Type
  TyCons :: Variable -> Type
  TyApp  :: Type -> Type -> Type
  TyLazy :: Type -> Type
  TyOpt  :: Type -> Type
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
`fix` term is actually a let. For ML we also introduct Lazy and Force. -}

data Term where
  Let    :: Variable -> Term -> Term -> Term
  Lazy   :: Term -> Term
  Force  :: Term -> Term
  Lit    :: Int -> Term
  Add    :: Term -> Term -> Term
  Var    :: Variable -> Term
  Lam    :: Variable -> Term -> Term
  App    :: Term -> Term -> Term
  Cons   :: Variable -> Term
  Case   :: Term -> [(Pattern,Term)] -> Term
  Try    :: Term -> (Variable,Term) -> Term
  Raise  :: Variable -> Term
  Proj   :: Variable -> Term -> Term
  Record :: [(Variable,Term)] -> Term
  Fail   :: Term
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
  pp pgm = "open Lazy\n"
         <-> (vmconcat (map ppTyDecl . pgmTyDecls $ pgm))
         <-> "exception Unmatched"
         <-> "let unmatched = lazy (raise Unmatched);;"
         <-> (vmconcat . fmap pp . pgmFunDecls $ pgm)
         <-> ("\nlet prog =" <-> indent 1 ((\t -> ppTerm t 2 9) . pgmTerm $ pgm) <> ";;")
         <-> "\nprint_int prog;;\nprint_newline ();;\n"

instance Pretty FunDecl where
  pp fd = "let"
        <+> (unVariable . funName $ fd)
        <+> (smconcat . fmap (allLower . unVariable) . funArgs $ fd)
        <+> "="
        <-> indent 1 (ppTerm (funRhs fd) 1 9) <> ";;"

ppTyDecl :: Either DataTyCons RecordTyCons -> String
ppTyDecl = either ppDataDecl ppRecordDecl

ppDataDecl :: DataTyCons -> String
ppDataDecl tc =
  (smconcat [ "type"
            , parens . stringmconcat " , " . fmap unVariable . dataFVars $ tc
            , allLower . unVariable . dataName $ tc
            ]
  )
  <-> (vmconcat . fmap ppDataCon . dataCons $ tc)
  <> "\n"

ppDataCon :: DataCon -> String
ppDataCon dc =
  indent 1 ((unVariable . conName $ dc) <+> ":" <+> flip ppType 9 . conType $ dc)

ppRecordDecl :: RecordTyCons -> String
ppRecordDecl r
  =   "type"
  <+> parens (stringmconcat " , " . fmap (("'"<>). pp) . recordFVars $ r)
  <+> (allLower . pp . recordName $ r)
  <> indent 1 "="
  <> indent 1 "{" <+> smconcat (fmap ((<>";") . ppRecordField) . recordFields $ r)
  <> indent 1 "}"

ppRecordField :: Field -> String
ppRecordField f = pp (fieldName f)
  <+> ":"
  <+> (flip ppType 9 . fieldType $ f)

ppType :: Type -> Int -> String
ppType TyInt       _ = "int"
ppType (TyArr a b) p = ppPrec 1 p (ppType a p <+> "->" <+> ppType b p)
ppType (TyVar s)   _ = "'" <> allLower (unVariable s)
ppType (TyCons s)  _ = allLower (unVariable s)
ppType (TyApp a b) p = ppPrec 9 p (ppType a p <+> ppType b p)
ppType (TyLazy a)  p = parens (ppType a p) <+> "lazy_t"
ppType (TyOpt a)   p = parens (ppType a p) <+> "option"

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p = smconcat ["let",unVariable s,"="
                                    ,ppTerm a i p,"in"]
                           <-> indent i (ppTerm b i p)
ppTerm (Lazy t)      i p = ppPrec 10 p ("lazy" <+> parens (ppTerm t i p))
ppTerm (Force t)     i p = ppPrec 10 p ("force" <+> parens (ppTerm t i p))

ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = unVariable s
ppTerm (Lam s t)     i p = parens ( "fun" <+> allLower (unVariable s) <+> "->"
                                  <-> indent i (ppTerm t (i+1) p))
ppTerm (App a b)     i p = parens (ppTerm a i 9 <+> ppTerm b i p)
ppTerm (Cons s)      _ _ = unVariable s
{- only exceptions can be upper case -}
ppTerm (Try a (v,b)) i p =
  "try" <+> ppTerm a i p <+> "with"
    <-> indent (i+1) (unVariable v <+> "->" <+> ppTerm b (i+1) p)
ppTerm (Raise v)     _ _ = parens . ("raise"<+>) . unVariable $ v
ppTerm Fail          _ _ = "unmatched"
ppTerm (Case t alts) i p =
  "match" <+> ppTerm t i 0 <+> "with"
    <-> indent (i+1) (stringmconcat ("\n" <> indent i "| ") . fmap ppAlt $ alts)
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (pat,t') = ppPattern pat
                         <+> "->"
                         <-> indent (i+2) (ppTerm t' (i+2) p)
        ppPattern :: Pattern -> String
        ppPattern PWild = "_"
        ppPattern (PVar s) = allLower (unVariable s)
        ppPattern (PCons s vs) = unVariable s <+> (smconcat . map unVariable $ vs)
ppTerm (Proj v a)    i p = parens (ppTerm a i p) <> "." <> unVariable v
ppTerm (Record fs)   i p = braces . pad . smconcat . fmap ppField $ fs
  where ppField (v,a) = unVariable v <+> "=" <+> ppTerm a (i+1) p <> ";"

--------------------------------------------------------------------------------
--                              Translation                                   --
--------------------------------------------------------------------------------


instance Translate Program where
  translate = trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: D.Program FlatTerm -> Program
trans dpgm =
  let (decls',fds) = foldr (\d (ds,fds') ->
                           let (d',fds'') = transDecl d
                           in  (d':ds,fds'++fds'') )
                         ([],[])
                         (D.pgmDecls dpgm)
  in Pgm { pgmTyDecls = decls'
         , pgmFunDecls = fds
         , pgmTerm = transTerm . D.pgmTerm $ dpgm }

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
  (Left (DataTyCons (Ty.posTyName $ d)
          (Ty.posTyFVars d)
          (fmap mkDataCon . Ty.injections $ d)), [])
  where mkDataCon :: Ty.Injection -> DataCon
        mkDataCon inj = DataCon (Ty.injName inj)
                                (transType . Ty.injType $ inj)

transDecl (Left d)  =
  (Right (RecordTyCons name
           (Ty.negTyFVars d)
           (fmap mkRecordField (Ty.projections d)))
  , addSetAndObs (Ty.projections d))
  where name = Ty.negTyName $ d
        pname p = Variable "get" <> Ty.projName p

        addSetAndObs :: [Ty.Projection] -> [FunDecl]
        addSetAndObs [] = []
        addSetAndObs (p:ps) =  [ mkSetter p, mkObserver p ]
                               <> addSetAndObs ps

        mkSetter,mkObserver :: Ty.Projection -> FunDecl
        mkSetter p = FunDecl
          { funName = Variable "set" <> Ty.projName p
          , funArgs = [Variable "cd", Variable "br"]
          , funRhs  =
              Try
                (Let (Variable "cdn")
                    ( Record
                    . fmap (\p' ->
                            ( Variable "get" <> Ty.projName p'
                            , case p == p' of
                                True -> App (Cons (Variable "Some"))
                                            (Var (Variable "br"))
                                False -> Proj (Variable "get" <> Ty.projName p')
                                              (Force (Var (Variable "cd")))))
                    . Ty.projections
                    $ d )
                    (Lazy (Var (Variable "cdn"))))
                (Variable "Unmatched",(Lazy ( Record
                                            . fmap (\p' ->
                                                      ( Variable "get" <> Ty.projName p'
                                                      , case p == p' of
                                                          True -> App (Cons (Variable "Some"))
                                                                      (Var (Variable "br"))
                                                          False -> Cons (Variable "None")))
                                            . Ty.projections
                                            $ d )))
          }
        mkObserver p = FunDecl
          { funName = Variable "obs" <> Ty.projName p
          , funArgs = [Variable "cd"]
          , funRhs  =
              Case (Proj (Variable "get" <> Ty.projName p)
                     (Force (Var (Variable "cd"))))
                   [(PCons (Variable "None") [], Force (Var (Variable "unmatched")))
                   ,(PCons (Variable "Some") [Variable "br"],Force (Var (Variable "br")))] }

        mkRecordField :: Ty.Projection -> Field
        mkRecordField p = Field (pname p)
                                ( TyOpt . TyLazy . typeCodom . transType
                                . Ty.projType $ p)

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
transTerm (FDest h) = Var (Variable "obs" <> h)
transTerm (FCoCase (q,u) d) = transCoalt (q,u) (transTerm d)
transTerm (FFail) = Fail

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs

transCoalt :: (FlatCopattern, FlatTerm) -> Term -> Term
transCoalt (FlatCopDest h,u) t = App (App (Var (Variable "set" <> h)) t)
                                           (Lazy . transTerm $ u)
transCoalt (FlatCopPat _,u) _ = transTerm u
