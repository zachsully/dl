module DL.Backend.Racket.Translation
  (rktCompile) where

import DL.Backend
import DL.Backend.Racket.Syntax
import qualified DL.General.Top  as Top
import qualified DL.General.Type as Ty
import DL.General.Variable
import DL.Flat.Syntax
import DL.Utils.StdMonad

rktCompile :: Backend
rktCompile = Backend trans

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
transDecl (Top.DataDecl d) =
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
                  lams = foldr (\v f -> Lam v . f) id (args :: [Variable])
              in
                 lams . SExpr (Top.injName i) . fmap Var $ args
          }

transDecl (Top.CodataDecl d)  =
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

transDecl (Top.IndexDecl _ _)  = error "transDecl{IndexDecl}"

transTerm :: FlatTerm -> Term
transTerm (FLet v a b) = Let v (transTerm a) (transTerm b)
transTerm (FFix v a) = let a' = transTerm a in Let v a' a'
transTerm (FVar v) = Var v
transTerm (FAnn t _) = transTerm t

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
transTerm (FShift _ _) = error "transTerm{FShift}"
transTerm (FPrompt t) = transTerm t

transTerm (FObsApp e t) = App (transTerm t) (transTerm e)
transTerm (FObsDest h t) = App (Var (Variable "obs" <> h)) (transTerm t)
transTerm (FObsCut _ _) = error "transTerm{FlatObsCut}"

transPat :: FlatPattern -> Pattern
transPat (FlatPatVar v)     = PVar v
transPat (FlatPatCons k vs) = PCons k vs
