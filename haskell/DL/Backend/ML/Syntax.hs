{-# LANGUAGE GADTs #-}
module DL.Backend.ML.Syntax where

import qualified DL.Syntax.Type as Ty
import qualified DL.Syntax.Top  as Top
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

--------------------------------------------------------------------------------
--                              Translation                                   --
--------------------------------------------------------------------------------


instance Translate Program where
  translate = trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: Top.Program FlatTerm -> Program
trans dpgm =
  let negTys = foldr (\(Top.Decl d) acc ->
                        case d of
                          Right _ -> acc
                          Left d' -> pure (Top.negTyName d') <> acc
                     )
                     []
                     (Top.pgmDecls dpgm)
      (decls',fds) = foldr (\d (ds,fds') ->
                           let (d',fds'') = transDecl negTys d
                           in  (d':ds,fds'++fds'') )
                         ([],[])
                         (Top.pgmDecls dpgm)
  in Pgm { pgmTyDecls = decls'
         , pgmFunDecls = fds
         , pgmTerm = transTerm . Top.pgmTerm $ dpgm }

transType :: Ty.Type -> Type
transType Ty.TyInt       = TyInt
transType (Ty.TyArr a b) = TyArr (transType a) (transType b)
transType (Ty.TyApp a b) = TyApp (transType a) (transType b)
transType (Ty.TyVar v)   = TyVar v
transType (Ty.TyCons k)  = TyCons k

{- Codata is always wrapped in an optional value -}
wrapOptNegTy :: [Variable] -> Type -> Type
wrapOptNegTy negTys ty =
  case isNeg ty of
    True  -> TyOpt ty
    False -> ty
  where isNeg (TyVar v) = elem v negTys
        isNeg (TyCons v) = elem v negTys
        isNeg (TyApp a _) = isNeg a
        isNeg _ = False

typeDom :: Type -> Type
typeDom (TyArr _ b) = b
typeDom x = error ("type" <+> pp x <+> "is not a projection")

transDecl
  :: [Variable]
  -> Top.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl negTys (Top.Decl (Right d)) =
  (Left (DataTyCons (Top.posTyName $ d)
          (Top.posTyFVars d)
          (fmap mkDataCon . Top.injections $ d)), fmap wrapFun . Top.injections $ d)
  where mkDataCon :: Top.Injection -> DataCon
        mkDataCon inj = DataCon (Top.injName inj)
                                (  curryArgs
                                 . wrapOptNegTy negTys
                                 . transType
                                 . Top.injType
                                 $ inj )

        curryArgs :: Type -> Type
        curryArgs (TyArr a b) =
          case b of
            TyArr b' c' ->
              case curryArgs (TyArr b' c') of
                TyPair b'' c'' -> TyPair (TyPair a b'') c''
                _ -> TyPair a b'
            _ -> a
        curryArgs x = x

        wrapFun :: Top.Injection -> FunDecl
        wrapFun i = FunDecl
          { funName = Variable "wrap" <> Top.injName i
          , funArgs = foldrWithIndex (\j s acc -> acc <> [Variable (s <> show j)])
                                     []
                                     (replicate (Ty.arity . Top.injType $ i) "x")
          , funRhs  =
              case replicate (Ty.arity . Top.injType $ i) "x" of
                [] -> (Var (Top.injName i))
                (x:xs) -> App (Var (Top.injName i)) $
                  foldrWithIndex (\j s acc -> Pair acc (Var (Variable (s <> show (j+1)))))
                                 (Var (Variable (x <> "0")))
                                 xs
          }

transDecl negTys (Top.Decl (Left d))  =
  (Right (RecordTyCons name
           (Top.negTyFVars d)
           (fmap mkRecordField (Top.projections d)))
  , addSetAndObs (Top.projections d))
  where name = Top.negTyName d
        pname p = Variable "get" <> Top.projName p
        _some x = App (Cons (Variable "Some")) x
        _none = (Cons (Variable "None"))

        addSetAndObs :: [Top.Projection] -> [FunDecl]
        addSetAndObs [] = []
        addSetAndObs (p:ps) =  [ mkSetter p, mkObserver p ]
                               <> addSetAndObs ps

        mkSetter,mkObserver :: Top.Projection -> FunDecl
        mkSetter p = FunDecl
          { funName = Variable "set" <> Top.projName p
          , funArgs = [Variable "ocd", Variable "br"]
          , funRhs  =
              Case (Var (Variable "ocd"))
                   [ ( PCons (Variable "None") []
                     , _some $
                       ( Record
                       . fmap (\p' ->
                                  ( Variable "get" <> Top.projName p'
                                  , case p == p' of
                                      True -> _some (Var (Variable "br"))
                                      False -> _none))
                       . Top.projections
                       $ d )
                     )
                   , ( PCons (Variable "Some") [Variable "cd"]
                     , _some $
                       ( Record
                       . fmap (\p' ->
                                  ( Variable "get" <> Top.projName p'
                                  , case p == p' of
                                      True -> _some (Var (Variable "br"))
                                      False -> Proj (Variable "get" <> Top.projName p')
                                                    (Var (Variable "cd"))))
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
                   [ ( PCons (Variable "None") [], Raise (Variable "UnmatchedCopattern"))
                   , ( PCons (Variable "Some") [Variable "cd"]
                     , Case  (Proj (Variable "get" <> Top.projName p)
                                   (Var (Variable "cd")))
                            [ ( PCons (Variable "None") [], Raise (Variable "UnmatchedCopattern"))
                            , ( PCons (Variable "Some") [Variable "br"]
                              , Force (Var (Variable "br")))
                            ]
                     )
                   ]
          }

        mkRecordField :: Top.Projection -> Field
        mkRecordField p = Field (pname p)
                                ( TyOpt
                                . TyLazy
                                . wrapOptNegTy negTys
                                . typeDom
                                . transType
                                . Top.projType $ p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
{-
   We need to add lazy and force here to get around Ocamls 'let rec'
   restrictions. Otherwise we get the error:

   Error: This kind of expression is not allowed as right-hand side of `let rec'
-}
transTerm (FFix v a) =
  let a' = Lazy . transTerm $ a in
    Let v (substTerm (Force (Var v)) (Var v) a') (Force (Var v))
transTerm (FVar v) = Var v

transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)

transTerm (FConsApp v fts) = foldr App (Var v) . fmap transTerm $ fts
transTerm (FCase t (p,u) (y,d)) = Case (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(PVar y,transTerm d)]
transTerm (FCaseEmpty t) = Case (transTerm t) []

transTerm (FCoalt (h,u) t) = App (App (Var (Variable "set" <> h))
                                      (transTerm t))
                                 (Lazy . transTerm $ u)
transTerm (FEmpty) = Fail
transTerm (FFun v t) = Lam v (transTerm t)
transTerm (FCocase (FlatObsFun e) t) = App (transTerm t) (transTerm e)
transTerm (FCocase (FlatObsDest h) t) = App (Var (Variable "obs" <> h))
                                            (transTerm t)

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs
