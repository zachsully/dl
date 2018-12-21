{-# LANGUAGE GADTs #-}
module DL.Backend.ML.Syntax where

import DL.General.Variable
import DL.Utils.Pretty

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
  TyPair :: Type -> Type -> Type
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
  Pair   :: Term -> Term -> Term
  Fail   :: Term
  deriving (Eq,Show)

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term]) -> Term
distributeArgs (k,ts) = foldl App (Cons k) ts

substTerm :: Term -> Term -> Term -> Term
substTerm s x y =
  case x == y of
    True -> s
    False ->
      case y of
        Let v a b -> Let v (substTerm s x a) (substTerm s x b)
        Lazy a -> Lazy (substTerm s x a)
        Force a -> Force (substTerm s x a)
        Lit i -> Lit i
        Add a b -> Add (substTerm s x a) (substTerm s x b)
        Var v -> Var v
        Lam v a -> Lam v (substTerm s x a)
        App a b -> App (substTerm s x a) (substTerm s x b)
        Cons c -> (Cons c)
        Case a alts -> Case (substTerm s x a)
                            (fmap (\(v,f) -> (v,substTerm s x f)) alts)
        Try a (v, b) -> Try (substTerm s x a) (v,substTerm s x b)
        Raise v -> Raise v
        Proj v a -> Proj v (substTerm s x a)
        Record fields -> Record . fmap (\(v,f) -> (v,substTerm s x f)) $ fields
        Pair a b -> Pair (substTerm s x a) (substTerm s x b)
        Fail -> Fail

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
         <-> "exception UnmatchedCopattern"
         <-> "let unmatched = None;;"
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
            , parens . stringmconcat " , " . fmap (("'"<>) . unVariable)
              . dataFVars $ tc
            , allLower . unVariable . dataName $ tc
            ]
  )
  <+> "="
  <+> (stringmconcat " | " . fmap ppDataCon . dataCons $ tc)
  <> "\n"

ppDataCon :: DataCon -> String
ppDataCon dc =
  indent 1 ((unVariable . conName $ dc) <+> "of" <+> pp . conType $ dc)

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
  <+> (pp . fieldType $ f)

instance Pretty Type where
  pp TyInt        = "int"
  pp (TyArr a b)  = pp a <+> "->" <+> pp b
  pp (TyVar s)    = "'" <> allLower (unVariable s)
  pp (TyCons s)   = allLower (unVariable s)
  pp (TyApp a b)  = pp b <+> pp a
  pp (TyLazy a)   = pp a <+> "lazy_t"
  pp (TyOpt a)    = pp a <+> "option"
  pp (TyPair a b) = parens (pp a <+> "*" <+> pp b)

{- The Int passed in is the indentation level and precedence -}
ppTerm :: Term -> Int -> Int -> String
ppTerm (Let s a b)   i p = smconcat ["let rec",unVariable s,"="
                                    ,ppTerm a i p,"in"]
                           <-> indent i (ppTerm b i p)
ppTerm (Lazy t)      i p = ppPrec 10 p ("lazy" <+> parens (ppTerm t i p))
ppTerm (Force t)     i p = ppPrec 10 p ("force" <+> parens (ppTerm t i p))

ppTerm (Lit n)       _ _ = show n
ppTerm (Add a b)     i p = ppPrec 6 p (ppTerm a i p <+> "+" <+> ppTerm b i p)
ppTerm (Var s)       _ _ = unVariable s
ppTerm (Lam s t)     i p = parens ( "fun" <+> allLower (unVariable s) <+> "->"
                                  <-> indent (i+1) (ppTerm t (i+1) p))
ppTerm (App a b)     i p = parens (ppTerm a i 9 <+> parens (ppTerm b i p))
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
        ppPattern (PCons s vs) =
          case fmap unVariable vs of
            [] -> unVariable s
            (v':vs') -> unVariable s
              <+> (foldl (\acc v'' -> "(" <> acc <+> "," <+> v'' <> ")") v' vs')
ppTerm (Proj v a)    i p = parens (ppTerm a i p) <> "." <> unVariable v
ppTerm (Record fs)   i p = braces . pad . smconcat . fmap ppField $ fs
  where ppField (v,a) = unVariable v <+> "=" <+> ppTerm a (i+1) p <> ";"
ppTerm (Pair a b)    i p = parens (ppTerm a i p <+> "," <+> ppTerm b i p)
