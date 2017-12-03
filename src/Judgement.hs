{-# LANGUAGE GADTs,KindSignatures #-}
module Judgement where

import Data.Monoid

import Utils
import TypeSyn
import DualSyn
import VariableSyn

data TypeScheme :: * where
  TyMono   :: Type -> TypeScheme
  TyForall :: TyVariable -> Type -> TypeScheme
  deriving Eq

instance Pretty TypeScheme where
  pp (TyMono ty)     = pp ty
  pp (TyForall v ty) = "∀" <+> v <> "." <+> pp ty

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

typeOfProgram :: Program Term -> Std Type
typeOfProgram (Pgm decls term) = infer (mkContext decls) term

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
                                 False -> error ("expecting type" <+> pp aTy1)
                             t -> error ("must be a function type, given" <+> pp t)
                         t -> error ("must be a function type, given" <+> pp t)
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
                                                            ,pp a,"and"
                                                            ,pp b])
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
unify a b = error (unwords ["cannot unify",pp a,"and",pp b])

--------------------------------------------------------------------------------
--                              Bidirectional Tc                              --
--------------------------------------------------------------------------------
{- Attempt at a bidirectional typechecker. We do not include declarations in the
~infer~ and ~check~ functions because we populate the Ctx with the necessary
information before running.
-}

-----------
-- infer --
-----------
infer :: Ctx -> Term -> Std Type
infer _ (Lit _) = return TyInt

infer c (Add a b) =
  do { check c a TyInt
     ; check c b TyInt
     ; return TyInt }

infer c (Var v) =
  case lookup v c of
    Just t -> return t
    Nothing -> unboundErr v

infer c (Fix _ t) = infer c t

infer c (Cons k) =
  case lookup k c of
    Just t -> return t
    Nothing -> unboundErr k

infer c (Dest h) =
  case lookup h c of
    Just t -> return t
    Nothing -> unboundErr h

infer c (App a b) =
  do { ty <- infer c a
     ; case ty of
         TyArr tyDom tyCod ->
           do { check c b tyDom
              ; return tyCod }
         _ -> typeErr ("operator must have a function type: " ++ pp a)
     }

infer _ (Case _ _) = unimplementedErr "infer{Case}"

infer _ (CoCase _) = unimplementedErr "infer{CoCase}"

-----------
-- check --
-----------

check :: Ctx -> Term -> Type -> Std ()
check _ (Lit _)   TyInt = return ()
check c (Add a b) TyInt = check c a TyInt >> check c b TyInt
check c (Var v)   ty    =
  case lookup v c of
    Just ty' ->
      case ty == ty' of
        True -> return ()
        False -> typeErr ("expected '" <+> v <+> "' to have type" <+> pp ty)
    Nothing -> unboundErr v
check c (Fix v t)  ty   = check ((v,ty):c) t ty
check _ (Cons _)   _    = error "check{Cons}"
check _ (Dest _)   _    = error "check{Dest}"
check _ (App _ _)  _    = error "check{App}"
check _ (Case _ _) _    = error "check{Case}"
check _ (CoCase _) _    = error "check{CoCase}"
check _ _ _ = failure "check{unknown error}"

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
