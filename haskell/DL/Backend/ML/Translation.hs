module DL.Backend.ML.Translation where

import qualified DL.Syntax.Type as Ty
import qualified DL.Syntax.Top  as Top
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Backend
import DL.Backend.ML.Syntax
import DL.Pretty
import DL.Utils

mlCompile :: Backend
mlCompile = Backend trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: Top.Program FlatTerm -> Program
trans dpgm =
  let negTys = foldr (\d acc ->
                        case d of
                          Top.DataDecl _ -> acc
                          Top.CodataDecl d' -> pure (Top.negTyName d') <> acc
                          Top.IndexDecl _ _ -> acc
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
transDecl negTys (Top.DataDecl d) =
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

transDecl negTys (Top.CodataDecl d)  =
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

transDecl _ (Top.IndexDecl _ _) = error "transDecl{IndexDecl}"

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
transTerm (FAnn t _) = transTerm t

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
transTerm (FCocase (FlatObsCut _) _) = error "transTerm{FlatObsCut}"
transTerm (FShift _ _) = error "transTerm{FShift}"
transTerm (FPrompt _) = error "transTerm{FPrompt}"

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs
