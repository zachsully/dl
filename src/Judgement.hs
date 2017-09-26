{-# LANGUAGE GADTs #-}
module Judgement where

import Data.Monoid

import Utils
import DualSyn

data TypeScheme where
  TyMono   :: Type -> TypeScheme
  TyForall :: TyVariable -> Type -> TypeScheme
  deriving (Show,Eq)

ppTypeScheme :: TypeScheme -> String
ppTypeScheme (TyMono ty)     = ppType ty
ppTypeScheme (TyForall v ty) = "forall" <+> v <> "." <+> ppType ty

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

typeOfProgram :: Program Term -> Type
typeOfProgram (Pgm decls term) = infer decls [] term

--------------------------------------------------------------------------------
--                                isType                                      --
--------------------------------------------------------------------------------
{- Checks whether a type is well formed -}

isType :: [Decl]              -- ^ A set of type signatures
       -> [(TyVariable,Type)] -- ^ A context of bindings of type variables
       -> Type
       -> Bool
isType _ _   TyInt         = True
isType s ctx (TyArr a b)   = isType s ctx a && isType s ctx b
isType s ctx (TyVar v)     = case lookup v ctx of
                               Just t -> isType s ctx t
                               Nothing -> False

{- A standalone type constructor is only valid if its arity is 0 -}
isType s _   (TyCons tc)   = case lookupDecl tc s of
                               Just d -> declArity d == 0
                               Nothing -> False
isType s ctx ty@(TyApp _ _) = case collectTyArgs ty of
                               Just (tc,tys) ->
                                 case lookupDecl tc s of
                                   Just d -> (all (isType s ctx) tys)
                                          && (length tys == declArity d)
                                   Nothing -> False
                               Nothing -> False

--------------------------------------------------------------------------------
--                              Infer TypeScheme                              --
--------------------------------------------------------------------------------
{- Type scheme inference with algorithm W. -}

inferTSProgram :: Program Term -> TypeScheme
inferTSProgram pgm = inferTS (mkContext . pgmDecls $ pgm)
                             (pgmTerm pgm)

inferTS :: [(Variable,Type)] -> Term -> TypeScheme
inferTS _ (Lit _)    = TyMono TyInt
inferTS c (Add a b)  = case (inferTS c a,inferTS c b) of
                         (TyMono TyInt, TyMono TyInt) -> TyMono TyInt
                         _ -> error "(+) requires it's arguments to be of type Int"
inferTS c (Var v)    = case lookup v c of
                         Just t -> TyMono t
                         Nothing -> error ("unbound variable " <> v)
inferTS c (Fix _ t)  = inferTS c t
inferTS c (App a b)  = case inferTS c a of
                         (TyMono (TyArr aTy0 aTy1)) ->
                           case inferTS c b of
                             TyMono bTy ->
                               case bTy == aTy0 of
                                 True -> TyMono aTy1
                                 False -> error ("expecting type" <+> ppType aTy1)
                             t -> error ("must be a function type, given" <+> ppTypeScheme t)
                         t -> error ("must be a function type, given" <+> ppTypeScheme t)
inferTS c (Cons k)   = case lookup k c of
                         Just t -> TyMono t
                         Nothing -> error ("unbound constructor " <> k)
inferTS c (Case e a) = let _ = inferTS c e
                           tyAlts = map inferTSAlt a
                       in case tyAlts of
                            [] -> error "cannot infer empty case"
                            (t:ts) -> case all (== t) ts of
                                        True -> t
                                        False -> error "all case branches must have the same type"
  where inferTSAlt :: (Pattern,Term) -> TypeScheme
        inferTSAlt (_,t) = inferTS c t

        -- inferTSPattern :: Pattern -> TypeScheme
        -- inferTSPattern PWild        = TyForall "x" (TyVar "x")
        -- inferTSPattern (PVar _)     = TyForall "x" (TyVar "x")
        -- inferTSPattern (PCons _ _)  = undefined

inferTS c (Dest h)   = case lookup h c of
                         Just t -> TyMono t
                         Nothing -> error ("unbound destructor " <> h)
inferTS c (CoCase a) = undefined c a

occurs :: TyVariable -> Type -> Bool
occurs _ TyInt       = False
occurs v (TyArr a b) = occurs v a || occurs v b
occurs v (TyVar v')  = v == v'
occurs v (TyCons k)  = v == k
occurs v (TyApp a b) = occurs v a || occurs v b

unify :: Type -> Type -> [(TyVariable,Type)]
unify a@(TyVar a') b@(TyVar b') = case a' == b' of
                                    True -> [(a',b)]
                                    False -> error (unwords ["cannot unify"
                                                            ,show a,"and"
                                                            ,show b])
unify (TyVar a') b = case occurs a' b of
                       True -> error "recursion in type"
                       False -> [(a',b)]
unify b (TyVar a') = case occurs a' b of
                       True -> error "recursion in type"
                       False -> [(a',b)]
unify (TyCons a) (TyCons b) = case a == b of
                                True -> []
                                False -> error ("unify tyCons" <> a <> " and " <> b)
unify (TyApp a b) (TyApp a' b') = unify a b <> unify a' b'
unify (TyArr a b) (TyArr a' b') = unify a b <> unify a' b'
unify a b = error (unwords ["cannot unify",show a,"and",show b])

--------------------------------------------------------------------------------
--                              Bidirectional Tc                              --
--------------------------------------------------------------------------------
{- Attempt at a bidirectional typechecker. Not complete and maybe not even
   necessary. -}
-----------
-- infer --
-----------
infer :: [Decl] -> Ctx -> Term -> Type
infer _ _ (Lit _) = TyInt

infer s c (Add a b) =
  case check s c a TyInt && check s c b TyInt of
    True -> TyInt
    False -> error "both arguments of + expect an TyInt"

infer _ c (Var v) =
  case lookup v c of
    Just t -> t
    Nothing -> error ("variable " ++ show v ++ " not bound")

infer s c (Fix _ t) = infer s c t

infer s _ (Cons k) = case do { d <- lookupDatum k s
                             ; case d of
                                 Left _ -> error "constructor as destructor"
                                 Right d' -> lookupInjection k . injections $ d'
                             } of
                       Just i -> injCod i
                       Nothing -> error ("unknown constructor " <> k)

infer s _ (Dest h) = case do { d <- lookupDatum h s
                             ; case d of
                                 Left d' -> lookupProjection h . projections $ d'
                                 Right _ -> error "destructor as constructor"
                             } of
                       Just p -> TyArr (projDom p) (projCod p)
                       Nothing -> error ("unknown destructor " <> h)

infer s c (App a b) =
  case infer s c a of
    TyArr tyDom tyCod ->
      case check s c b tyDom of
        True -> tyCod
        False -> error (show a ++ " expects arguments of type " ++ show tyDom)
    _ -> error ("operator must have a function type: " ++ show a)

infer _ _ (Case _ _) = error "infer{Case}"

infer _ _ (CoCase _) = error "infer{CoCase}"

-----------
-- check --
-----------

check :: [Decl] -> Ctx -> Term -> Type -> Bool
check _ _ (Lit _)   TyInt = True
check s c (Add a b) TyInt = check s c a TyInt && check s c b TyInt
check _ c (Var v)   ty    = case lookup v c of
                              Just ty' -> ty == ty'
                              Nothing -> False
check s c (Fix v t)  ty   = check s ((v,ty):c) t ty
check _ _ (Cons _)   _    = error "check{Cons}"
check _ _ (Dest _)   _    = error "check{Dest}"
check _ _ (App _ _)  _    = error "check{App}"
check _ _ (Case _ _) _    = error "check{Case}"
check _ _ (CoCase _) _    = error "check{CoCase}"
check _ _ _ _ = False

--------------------------------------------------------------------------------
--                                 Utils                                      --
--------------------------------------------------------------------------------

mkTyContext :: [Decl] -> [(TyVariable,Type)]
mkTyContext = undefined

mkContext :: [Decl] -> [(Variable,Type)]
mkContext [] = []
mkContext (d:ds) =
  (case d of
     Left neg -> map (\p -> (projName p, TyArr (projDom p) (projCod p)))
                    (projections neg)
     Right pos -> map (\i -> (injName i, injCod i)) (injections pos)
  ) <> (mkContext ds)

lookupDecl :: TyVariable -> [Decl] -> Maybe Decl
lookupDecl _ [] = Nothing
lookupDecl v ((Left d):ds) = case v == negTyName d of
                               True -> Just (Left d)
                               False -> lookupDecl v ds
lookupDecl v ((Right d):ds) = case v == posTyName d of
                               True -> Just (Right d)
                               False -> lookupDecl v ds

type Ctx = [(Variable,Type)]

lookupDatum :: Variable -> [Decl] -> Maybe Decl
lookupDatum _ [] = Nothing
lookupDatum h (Left  d:ds) =
  case lookupProjection h (projections d) of
    Just _ -> Just (Left d)
    Nothing -> lookupDatum h ds
lookupDatum k (Right d:ds) =
  case lookupInjection k (injections d) of
    Just _ -> Just (Right d)
    Nothing -> lookupDatum k ds

lookupProjection :: Variable -> [Projection] -> Maybe Projection
lookupProjection _ [] = Nothing
lookupProjection h (p:ps) = case projName p == h of
                             True -> Just p
                             False -> lookupProjection h ps

lookupInjection :: Variable -> [Injection] -> Maybe Injection
lookupInjection _ [] = Nothing
lookupInjection k (i:is) = case injName i == k of
                             True -> Just i
                             False -> lookupInjection k is
