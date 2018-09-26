module DL.Backend.Haskell.Translation
  (hsCompile) where

import DL.Backend
import DL.Backend.Haskell.Syntax
import qualified Data.Set as Set
import DL.Syntax.Type
import DL.Syntax.Top
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Utils
import DL.Pretty

hsCompile :: Backend
hsCompile = Backend trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: Program FlatTerm -> HsProgram
trans dpgm
  = HsPgm { hsPgmDecls = concatMap transDecl (pgmDecls dpgm)
          , hsPgmTerm  = transTerm . pgmTerm $ dpgm }

transType :: Type -> HsType
transType TyInt       = HsTyInt
transType (TyArr a b) = HsTyArr (transType a) (transType b)
transType (TyApp a b) = HsTyApp (transType a) (transType b)
transType (TyVar v)   = HsTyVar v
transType (TyCons k)  = HsTyCons k

transConstraint :: Constraint -> [HsConstraint]
transConstraint CTrue = []
transConstraint (CConj c1 c2) = transConstraint c1 ++ transConstraint c2
transConstraint (CEq t1 t2) = [HsCEq (transType t1) (transType t2)]
transConstraint (CNumeric ty) = [HsCNumeric (transType ty)]

typeCodom :: HsType -> HsType
typeCodom (HsTyArr _ b) = b
typeCodom x = error ("type" <+> pp x <+> "is not a projection")

transDecl :: Decl -> [HsDecl]
transDecl (DataDecl d) = [ HsDataDecl
                             $ HsData
                                 (posTyName d)
                                 (posTyFVars d)
                                 (fmap mkHsDataCon . injections $ d)]
  where mkHsDataCon :: Injection -> HsDataCon
        mkHsDataCon inj =
          let baseTy = transType . injType $ inj
              f = case injMConstraint inj of
                    Nothing -> id
                    Just c -> HsTyForall
                                (Set.toList (Set.union (fvs c) (fvs . injType $ inj)))
                                (transConstraint c)
          in
            HsDataCon (injName inj) (f baseTy)

transDecl (CodataDecl d)  =
  (  HsRecordDecl
   $ HsRecord
       name
       (negTyFVars d)
       (fmap mkHsRecordField (projections d)))
  : (fmap (HsFunDecl . setter) . projections $ d)
  where name = negTyName d
        pname p = Variable "_" <> projName p

        setter :: Projection -> HsFun
        setter p = HsFun
          { hsFunName = Variable "set_" <> projName p
          , hsFunArgs = [Variable "cd", Variable "br"]
          , hsFunType = Nothing
          , hsFunRhs  =
              foldl (\c p' ->
                        let t = case p == p' of
                                  True  -> HsVar (Variable "br")
                                  False -> HsApp (HsVar (pname p')) (HsVar (Variable "cd"))
                        in HsApp c t
                    )
                    (HsCons name)
                    (projections d)
          }

        mkHsRecordField :: Projection -> HsField
        mkHsRecordField p = HsField (pname p)
                                (case projMConstraint p of
                                   Nothing -> []
                                   Just c  -> transConstraint c
                                )
                                (typeCodom . transType . projType $ p)

transDecl (IndexDecl n args) = [HsDataDecl (HsData n args [])]

transTerm :: FlatTerm -> HsTerm
transTerm (FLet v a b) = HsLet v (transTerm a) (transTerm b)
transTerm (FFix v a) = let a' = transTerm a in HsLet v a' a'
transTerm (FVar v) = HsVar v

transTerm (FLit i) = HsLit i
transTerm (FAdd a b) = HsAdd (transTerm a) (transTerm b)

transTerm (FConsApp v fts) = foldr HsApp (HsVar v) . fmap transTerm $ fts
transTerm (FCase t (p,u) (y,d)) = HsCase (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(HsPVar y,transTerm d)]
transTerm (FCaseEmpty t) = HsApp HsFail (transTerm t)

transTerm (FCoalt (h,u) t) = HsApp (HsApp (HsVar (Variable "set_" <> h))
                                     (transTerm t))
                               (transTerm u)
transTerm (FEmpty) = HsFail
transTerm (FFun v t) = HsLam v (transTerm t)
transTerm (FCocase (FlatObsFun e) t) = HsApp (transTerm t) (transTerm e)
transTerm (FCocase (FlatObsDest h) t) = HsApp (HsVar (Variable "_" <> h))
                                              (transTerm t)
transTerm (FCocase (FlatObsCut _) _) = error "transTerm{FlatObsCut}"
transTerm (FShift _ _) = error "transTerm{FShift}"
transTerm (FPrompt t) = transTerm t

transPat :: FlatPattern -> HsPattern
transPat (FlatPatVar v)     = HsPVar v
transPat (FlatPatCons k vs) = HsPCons k vs
