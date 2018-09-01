{-# LANGUAGE GADTs #-}
module DL.Backend.Racket.Syntax where

import qualified DL.Syntax.Top  as Top
import qualified DL.Syntax.Type as Ty
import DL.Syntax.Flat
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
trans :: Top.Program FlatTerm -> Program
trans dpgm =
  let (decls',fds) = foldr (\d (ds,fds') ->
                           let (d',fds'') = transDecl d
                           in  (d':ds,fds'++fds'') )
                         ([],[])
                         (Top.pgmDecls dpgm)
  in Pgm { pgmTyDecls = decls'
         , pgmFunDecls = fds
         , pgmTerm = transTerm . Top.pgmTerm $ dpgm }

transDecl
  :: Top.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl (Top.Decl (Right d)) =
  (Left (DataTyCons (Top.posTyName $ d)
          (Top.posTyFVars d)
          (fmap mkDataCon . Top.injections $ d)), fmap wrapFun . Top.injections $ d)
  where mkDataCon :: Top.Injection -> DataCon
        mkDataCon inj = DataCon (Top.injName inj)

        wrapFun :: Top.Injection -> FunDecl
        wrapFun i = FunDecl
          { funName = Variable "wrap" <> Top.injName i
          , funArgs = []
          , funRhs  =
              let arity' = Ty.arity . Top.injType $ i
                  args = foldrWithIndex (\j x acc ->
                                           (Variable (x <> show j)):acc)
                                        []
                                        (replicate arity' "x")
                  lams :: Term -> Term
                  lams = foldr (\v f -> Lam v . f) id args
              in
                 lams . SExpr (Top.injName i) . fmap Var $ args
          }

transDecl (Top.Decl (Left d))  =
  (Right (RecordTyCons name
           (Top.negTyFVars d)
           (fmap mkRecordField (Top.projections d)))
  , addSetAndObs (Top.projections d))
  where name = Top.negTyName $ d
        pname p = (Variable "get") <> Top.projName p
        _some x = SExpr (Variable "some") [x]
        _none = SExpr (Variable "none") []

        addSetAndObs :: [Top.Projection] -> [FunDecl]
        addSetAndObs [] = []
        addSetAndObs (p:ps) =  [ mkGetter p, mkSetter p, mkObserver p ]
                               <> addSetAndObs ps

        mkGetter,mkSetter,mkObserver :: Top.Projection -> FunDecl
        mkGetter p = FunDecl
          { funName = Variable "get" <> Top.projName p
          , funArgs = []
          , funRhs  =
              Lam (Variable "cd") $
              Case (Var (Variable "cd"))
                   [ ( PCons name
                         (fmap (\p' ->
                                 case p == p' of
                                   True -> Variable "x"
                                   False -> Variable "_")
                          . Top.projections
                          $ d )
                     , Var (Variable "x"))
                   ]
          }

        mkSetter p = FunDecl
          { funName = Variable "set" <> Top.projName p
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
                       . Top.projections
                       $ d )
                     )
                   , ( PCons (Variable "some") [Variable "cd"]
                     , _some $
                       ( SExpr name
                       . fmap (\p' ->
                                 case p == p' of
                                   True -> _some (Var (Variable "br"))
                                   False -> Proj (Variable "get" <> Top.projName p')
                                                 (Var (Variable "cd")))
                       . Top.projections
                       $ d )
                    )
                   ]
          }
        mkObserver p = FunDecl
          { funName = Variable "obs" <> Top.projName p
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

        mkRecordField :: Top.Projection -> Field
        mkRecordField p = Field (Top.projName p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FFix v a) = let a' = transTerm a in Let v a' a'
transTerm (FVar v) = Var v

transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)

transTerm (FConsApp v fts) = foldr App (Var (Variable "wrap" <> v))
                           . fmap transTerm $ fts
transTerm (FCase t (p,u) (y,d)) = Case (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(PVar y,transTerm d)]
transTerm (FCaseEmpty t) = Case (transTerm t) []

transTerm (FCoalt (h,u) t) = App (App (Var (Variable "set" <> h)) (transTerm t))
                                 (Lazy . transTerm $ u)
transTerm (FEmpty) = Fail
transTerm (FFun v t) = Lam v (transTerm t)
transTerm (FCocase (FlatObsFun e) t) = App (transTerm t) (transTerm e)
transTerm (FCocase (FlatObsDest h) t) = App (Var (Variable "obs" <> h))
                                            (transTerm t)

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs
