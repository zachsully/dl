{-# LANGUAGE GADTs #-}
module DL.Backend.Racket.Syntax where

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

data DataTyCons
  = DataTyCons
  { dataName  :: Variable
  , dataFVars :: [Variable]
  , dataCons  :: [DataCon] }
  deriving (Eq,Show)

data DataCon = DataCon { conName :: Variable }
  deriving (Eq,Show)

data RecordTyCons
  = RecordTyCons
  { recordName   :: Variable
  , recordFVars  :: [Variable]
  , recordFields :: [Field] }
  deriving (Eq,Show)

data Field = Field { fieldName :: Variable }
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
  Raise  :: Variable -> Term
  Proj   :: Variable -> Term -> Term
  SExpr  :: Variable -> [Term] -> Term
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
  pp pgm =   "#lang racket"
         <-> "(require racket/promise)"
         <-> ""
         <-> "(define unmatched 'none)"
         <-> (vmconcat . fmap pp . pgmFunDecls $ pgm)
         <-> ""
         <-> (parens ("define prog" <-> (indent 1 . (\t -> ppTerm t 2) . pgmTerm $ pgm)))
         <-> ""
         <-> "prog"

instance Pretty FunDecl where
  pp fd = parens
        $   "define"
        <+> case funArgs fd of
              [] -> unVariable . funName $ fd
              as -> parens ((unVariable . funName $ fd)
                            <+> (smconcat . fmap (unVariable) $ as))
        <-> indent 1 (ppTerm (funRhs fd) 1)

ppTyDecl :: Either DataTyCons RecordTyCons -> String
ppTyDecl = either ppDataDecl ppRecordDecl

ppDataDecl :: DataTyCons -> String
ppDataDecl tc =
  (smconcat [ "type"
            , parens . stringmconcat " , " . fmap (("'"<>) . unVariable)
              . dataFVars $ tc
            , unVariable . dataName $ tc
            ]
  )
  <+> "="
  <+> (stringmconcat " | " . fmap ppDataCon . dataCons $ tc)
  <> "\n"

ppDataCon :: DataCon -> String
ppDataCon = indent 1 . unVariable . conName

ppRecordDecl :: RecordTyCons -> String
ppRecordDecl r
  =   parens
  $   "struct"
  <+> (pp . recordName $ r)
  <+> parens (smconcat . fmap ppRecordField . recordFields $ r)

ppRecordField :: Field -> String
ppRecordField f = pp (fieldName f)


{- For racket, the Int passed in is the indentation level -}
ppTerm :: Term -> Int -> String
ppTerm (Let s a b) i = parens ("letrec"
                                <+> parens (parens (unVariable s <+> (ppTerm a i)))
                                <-> indent i (ppTerm b i))
ppTerm (Lazy t) i = parens ("lazy" <+> (ppTerm t i))
ppTerm (Force t) i = parens ("force" <+> (ppTerm t i))
ppTerm (Lit n) _ = show n
ppTerm (Add a b) i = parens ("+" <+> (ppTerm a i) <+> (ppTerm b i))
ppTerm (Var s) _ = unVariable s
ppTerm (Lam s t) i = parens ( "lambda"
                              <+> parens (unVariable s)
                              <-> indent (i+1) (ppTerm t (i+1)))
ppTerm (App a b) i = parens (ppTerm a i <+> ppTerm b i)
ppTerm (Cons s) _ = unVariable s
ppTerm (Raise v) _ = parens . ("error"<+>) . unVariable $ v
ppTerm Fail _ = "unmatched"
ppTerm (Case t alts) i = parens
                       $ "match" <+> ppTerm t i
                       <-> (vmconcat . fmap (indent (i+1) . ppAlt) $ alts )
  where ppAlt :: (Pattern,Term) -> String
        ppAlt (pat,t') =   brackets
                       $   ppPattern pat
                       <-> indent (i+2) (ppTerm t' (i+3))
        ppPattern :: Pattern -> String
        ppPattern PWild = "`,_"
        ppPattern (PVar s) = "`," <> (unVariable s)
        ppPattern (PCons s vs) =
          case fmap unVariable vs of
            [] -> "`" <> unVariable s
            vs' -> "`" <> (parens $ smconcat ([unVariable s]<>fmap (","<>) vs'))
ppTerm (Proj v a) i = parens (unVariable v <+> (ppTerm a i))
ppTerm (SExpr c fs) i = ("`"<>)
                      . parens
                      . (unVariable c <+>)
                      . smconcat
                      . fmap ((","<>) . flip ppTerm (i+1))
                      $ fs
