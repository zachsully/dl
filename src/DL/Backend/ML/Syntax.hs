{-# LANGUAGE GADTs #-}
module DL.Backend.ML.Syntax where

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
trans :: D.Program FlatTerm -> Program
trans dpgm =
  let negTys = foldr (\d acc ->
                        case d of
                          Right _ -> acc
                          Left d' -> pure (Ty.negTyName d') <> acc
                     )
                     []
                     (D.pgmDecls dpgm)
      (decls',fds) = foldr (\d (ds,fds') ->
                           let (d',fds'') = transDecl negTys d
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
  -> D.Decl
  -> (Either DataTyCons RecordTyCons,[FunDecl])
transDecl negTys (Right d) =
  (Left (DataTyCons (Ty.posTyName $ d)
          (Ty.posTyFVars d)
          (fmap mkDataCon . Ty.injections $ d)), fmap wrapFun . Ty.injections $ d)
  where mkDataCon :: Ty.Injection -> DataCon
        mkDataCon inj = DataCon (Ty.injName inj)
                                (  curryArgs
                                 . wrapOptNegTy negTys
                                 . transType
                                 . Ty.injType
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

        wrapFun :: Ty.Injection -> FunDecl
        wrapFun i = FunDecl
          { funName = Variable "wrap" <> Ty.injName i
          , funArgs = foldrWithIndex (\j s acc -> acc <> [Variable (s <> show j)])
                                     []
                                     (replicate (arity . Ty.injType $ i) "x")
          , funRhs  =
              case replicate (arity . Ty.injType $ i) "x" of
                [] -> (Var (Ty.injName i))
                (x:xs) -> App (Var (Ty.injName i)) $
                  foldrWithIndex (\j s acc -> Pair acc (Var (Variable (s <> show (j+1)))))
                                 (Var (Variable (x <> "0")))
                                 xs
          }

transDecl negTys (Left d)  =
  (Right (RecordTyCons name
           (Ty.negTyFVars d)
           (fmap mkRecordField (Ty.projections d)))
  , addSetAndObs (Ty.projections d))
  where name = Ty.negTyName d
        pname p = Variable "get" <> Ty.projName p
        _some x = App (Cons (Variable "Some")) x
        _none = (Cons (Variable "None"))

        addSetAndObs :: [Ty.Projection] -> [FunDecl]
        addSetAndObs [] = []
        addSetAndObs (p:ps) =  [ mkSetter p, mkObserver p ]
                               <> addSetAndObs ps

        mkSetter,mkObserver :: Ty.Projection -> FunDecl
        mkSetter p = FunDecl
          { funName = Variable "set" <> Ty.projName p
          , funArgs = [Variable "ocd", Variable "br"]
          , funRhs  =
              Case (Var (Variable "ocd"))
                   [ ( PCons (Variable "None") []
                     , _some $
                       ( Record
                       . fmap (\p' ->
                                  ( Variable "get" <> Ty.projName p'
                                  , case p == p' of
                                      True -> _some (Var (Variable "br"))
                                      False -> _none))
                       . Ty.projections
                       $ d )
                     )
                   , ( PCons (Variable "Some") [Variable "cd"]
                     , _some $
                       ( Record
                       . fmap (\p' ->
                                  ( Variable "get" <> Ty.projName p'
                                  , case p == p' of
                                      True -> _some (Var (Variable "br"))
                                      False -> Proj (Variable "get" <> Ty.projName p')
                                                    (Var (Variable "cd"))))
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
                   [ ( PCons (Variable "None") [], Raise (Variable "UnmatchedCopattern"))
                   , ( PCons (Variable "Some") [Variable "cd"]
                     , Case  (Proj (Variable "get" <> Ty.projName p)
                                   (Var (Variable "cd")))
                            [ ( PCons (Variable "None") [], Raise (Variable "UnmatchedCopattern"))
                            , ( PCons (Variable "Some") [Variable "br"]
                              , Force (Var (Variable "br")))
                            ]
                     )
                   ]
          }

        mkRecordField :: Ty.Projection -> Field
        mkRecordField p = Field (pname p)
                                ( TyOpt
                                . TyLazy
                                . wrapOptNegTy negTys
                                . typeDom
                                . transType
                                . Ty.projType $ p)

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FLit i) = Lit i
transTerm (FAdd a b) = Add (transTerm a) (transTerm b)
transTerm (FVar v) = Var v
{-
   We need to add lazy and force here to get around Ocamls 'let rec'
   restrictions. Otherwise we get the error:

   Error: This kind of expression is not allowed as right-hand side of `let rec'
-}
transTerm (FFix v a) =
  let a' = Lazy . transTerm $ a in
    Let v (substTerm (Force (Var v)) (Var v) a') (Force (Var v))
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
