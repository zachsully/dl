{-# LANGUAGE GADTs #-}
module DL.Backend.Racket.Syntax where

import Data.Monoid

import qualified DL.Syntax.Term as D
import qualified DL.Syntax.Type as Ty
import DL.Flatten
import DL.Translation
import DL.Syntax.Variable
import DL.Pretty
import DL.Utils

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

transDecl
  :: D.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl (Right d) =
  (Left (DataTyCons (Ty.posTyName $ d)
          (Ty.posTyFVars d)
          (fmap mkDataCon . Ty.injections $ d)), fmap wrapFun . Ty.injections $ d)
  where mkDataCon :: Ty.Injection -> DataCon
        mkDataCon inj = DataCon (Ty.injName inj)

        wrapFun :: Ty.Injection -> FunDecl
        wrapFun i = FunDecl
          { funName = Variable "wrap" <> Ty.injName i
          , funArgs = []
          , funRhs  =
              let arity' = arity . Ty.injType $ i
                  args = foldrWithIndex (\j x acc ->
                                           (Variable (x <> show j)):acc)
                                        []
                                        (replicate arity' "x")
                  lams :: Term -> Term
                  lams = foldr (\v f -> Lam v . f) id args
              in
                 lams . SExpr (Ty.injName i) . fmap Var $ args
          }

transDecl (Left d)  =
  (Right (RecordTyCons name
           (Ty.negTyFVars d)
           (fmap mkRecordField (Ty.projections d)))
  , addSetAndObs (Ty.projections d))
  where name = Ty.negTyName $ d
        pname p = (Variable "get") <> Ty.projName p
        _some x = SExpr (Variable "some") [x]
        _none = SExpr (Variable "none") []

        addSetAndObs :: [Ty.Projection] -> [FunDecl]
        addSetAndObs [] = []
        addSetAndObs (p:ps) =  [ mkGetter p, mkSetter p, mkObserver p ]
                               <> addSetAndObs ps

        mkGetter,mkSetter,mkObserver :: Ty.Projection -> FunDecl
        mkGetter p = FunDecl
          { funName = Variable "get" <> Ty.projName p
          , funArgs = []
          , funRhs  =
              Lam (Variable "cd") $
              Case (Var (Variable "cd"))
                   [ ( PCons name
                         (fmap (\p' ->
                                 case p == p' of
                                   True -> Variable "x"
                                   False -> Variable "_")
                          . Ty.projections
                          $ d )
                     , Var (Variable "x"))
                   ]
          }

        mkSetter p = FunDecl
          { funName = Variable "set" <> Ty.projName p
          , funArgs = []
          , funRhs  =
              Lam (Variable "ocd") $
              Lam (Variable "br") $
              Case (Var (Variable "ocd"))
                   [ ( PCons (Variable "none") []
                     , _some $
                       ( SExpr name
                       . fmap (\p' ->
                                 case p == p' of
                                   True -> _some (Var (Variable "br"))
                                   False -> _none)
                       . Ty.projections
                       $ d )
                     )
                   , ( PCons (Variable "some") [Variable "cd"]
                     , _some $
                       ( SExpr name
                       . fmap (\p' ->
                                 case p == p' of
                                   True -> _some (Var (Variable "br"))
                                   False -> Proj (Variable "get" <> Ty.projName p')
                                                 (Var (Variable "cd")))
                       . Ty.projections
                       $ d )
                    )
                   ]
          }
        mkObserver p = FunDecl
          { funName = Variable "obs" <> Ty.projName p
          , funArgs = [Variable "ocd"]
          , funRhs  =
              Case (Var (Variable "ocd"))
                   [ ( PCons (Variable "none") [], Raise . Variable $ "\"unmatched (co)pattern\"")
                   , ( PCons (Variable "some") [Variable "cd"]
                     , Case  (Proj (pname p)
                                   (Var (Variable "cd")))
                            [ ( PCons (Variable "none") [], Raise . Variable $ "\"unmatched (co)pattern\"")
                            , ( PCons (Variable "some") [Variable "br"]
                              , Force (Var (Variable "br")))
                            ]
                     )
                   ]
          }

        mkRecordField :: Ty.Projection -> Field
        mkRecordField p = Field (Ty.projName p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)
transTerm (FVar v) = Var v
transTerm (FFix v a) = let a' = transTerm a in Let v a' a'
transTerm (FApp a b) = App (transTerm a) (transTerm b)
transTerm (FCons k) = Cons (Variable "wrap" <> k)
transTerm (FCase t (p,u) (y,d)) = Case (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(PVar y,transTerm d)]
transTerm (FDest h) = Var (Variable "obs" <> h)
transTerm (FCoCase (q,u) d) = transCoalt (q,u) (transTerm d)
transTerm (FFail) = Fail

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs

transCoalt :: (FlatCopattern, FlatTerm) -> Term -> Term
transCoalt (FlatCopDest h,u) t = App (App (Var (Variable "set" <> h)) t)
                                     (Lazy . transTerm $ u)
transCoalt (FlatCopPat p,u) _ =
  case p of
    FlatPatVar v ->
      Lam v (transTerm u)