module DL.Flat.Backend.Haskell.Translation
  (hsCompile) where

import qualified Data.Set as Set

import DL.Backend
import DL.General.Type
import DL.General.Top
import DL.General.Variable
import DL.Flat.Syntax
import DL.Flat.Backend.Haskell.Syntax
import DL.Utils.StdMonad
import DL.Utils.Pretty

hsCompile :: Backend FlatTerm
hsCompile = Backend trans

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
trans :: Program FlatTerm -> HsProgram
trans dpgm
  = HsPgm { hsPgmDecls = fixDecl : (concatMap transDecl (pgmDecls dpgm))
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

fixDecl :: HsDecl
fixDecl =
  let fVar = Variable "f"
      xVar = Variable "x"
  in HsFunDecl $ HsFun
  { hsFunName = Variable "fix"
  , hsFunArgs = [fVar]
  , hsFunType = Just (HsTyArr (HsTyArr (HsTyVar xVar) (HsTyVar xVar)) (HsTyVar xVar))
  , hsFunRhs  = HsLet xVar (HsApp (HsVar fVar) (HsVar xVar)) (HsVar xVar)
  }


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

transDecl (CodataDecl d) = recordDecl : (fmap mkSetter (projections d))
  where name :: Variable
        name = negTyName d

        mkProjName :: Projection -> Variable
        mkProjName p = Variable "_" <> projName p

        dataTy :: HsType
        dataTy = hsTyApps (HsTyCons name) (fmap HsTyVar (negTyFVars d))

        recordDecl :: HsDecl
        recordDecl = HsRecordDecl $ HsRecord
          { hsRecordName   = name
          , hsRecordFVars  = negTyFVars d
          , hsRecordFields = fmap mkField (projections d)
          }

        mkField :: Projection -> HsField
        mkField p =
          let ty = typeCodom . transType . projType $ p
              (cFvs,c') = case projMConstraint p of
                            Nothing -> (mempty,mempty)
                            Just c  -> (fvs c, transConstraint c)
              tyFvs = Set.toList (Set.difference (Set.union cFvs (fvs ty))
                                  (Set.fromList (negTyFVars d)))
          in HsField
          { hsFieldName        = mkProjName p
          , hsFieldFVars       = tyFvs
          , hsFieldConstraints = c'
          , hsFieldType        = ty
          }

        mkProjTy :: Projection -> HsType
        mkProjTy p =
          let ty = typeCodom . transType . projType $ p
              (cFvs,c') = case projMConstraint p of
                            Nothing -> (mempty,mempty)
                            Just c  -> (fvs c, transConstraint c)
              tyFvs = Set.toList (Set.difference (Set.union cFvs (fvs ty))
                                  (Set.fromList (negTyFVars d)))
          in case tyFvs == [] && c' == [] of
               True  -> ty
               False -> HsTyForall tyFvs c' ty

        mkSetter :: Projection -> HsDecl
        mkSetter p =
          let cdVar = Variable "_codata"
              projVar = Variable "_proj"
          in HsFunDecl $ HsFun
          { hsFunName = Variable "set_" <> projName p
          , hsFunArgs = [cdVar,projVar]
          , hsFunType = Just (HsTyArr dataTy (HsTyArr (mkProjTy p) dataTy))
          , hsFunRhs  =
              hsApps (HsCons name)
                     (fmap (\p' ->
                              case p == p' of
                                True  -> HsVar projVar
                                False -> HsApp (HsVar (mkProjName p')) (HsVar cdVar)
                           )
                           (projections d)
                     )
          }

transDecl (IndexDecl n args) = [HsDataDecl (HsData n args [])]

transTerm :: FlatTerm -> HsTerm
transTerm (FLet v a b) = HsLet v (transTerm a) (transTerm b)
transTerm (FFix v a) = HsApp (HsVar (Variable "fix")) (HsLam v (transTerm a))
transTerm (FVar v) = HsVar v

-- NOTA BENE[Hs Annotations] This is a nasty special case to please Haskell's
-- typechecker in the safestack programs. DL's type inference is more permissive
-- in deciding whether an indexed type requires an annotation. The important
-- examples here are "examples/source/safestack3.dl" and
-- "examples/source/safestack5.dl". The annotations on "mkStack" are not
-- necessary for DL, but we need to propogate them to satisfy Haskell.
transTerm (FAnn (FFix v a) ty)
  = HsLet v (transTerm a) (HsAnn (HsVar v) (transType ty))
transTerm (FAnn t ty) = HsAnn (transTerm t) (transType ty)

transTerm (FLit i) = HsAnn (HsLit i) HsTyInt
transTerm (FAdd a b) = HsAdd (transTerm a) (transTerm b)

transTerm (FConsApp v fts) = foldl HsApp (HsVar v) . fmap transTerm $ fts
transTerm (FCase t (p,u) (y,d)) = HsCase (transTerm t)
                                         [(transPat p, transTerm u)
                                         ,(HsPVar y,transTerm d)]
transTerm (FCaseEmpty t) = HsApp HsFail (transTerm t)

transTerm (FCoalt (h,u) t) = HsApp (HsApp (HsVar (Variable "set_" <> h))
                                     (transTerm t))
                               (transTerm u)
transTerm (FEmpty) = HsFail
transTerm (FFun v t) = HsLam v (transTerm t)
transTerm (FShift _ _) = error "transTerm{FShift}"
transTerm (FPrompt t) = transTerm t

transTerm (FObsApp e t) = HsApp (transTerm t) (transTerm e)
transTerm (FObsDest h t) = HsApp (HsVar (Variable "_" <> h))
                                              (transTerm t)
transTerm (FObsCut _ _) = error "transTerm{FlatObsCut}"
transTerm (FStreamCoiter _ _ _) = error "transTerm{FStreamCoiter}"


transPat :: FlatPattern -> HsPattern
transPat (FlatPatVar v)     = HsPVar v
transPat (FlatPatCons k vs) = HsPCons k vs
