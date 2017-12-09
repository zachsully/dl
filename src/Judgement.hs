{-# LANGUAGE GADTs,KindSignatures #-}
module Judgement where

import Prelude hiding (id)
import Data.Monoid
import Data.Set hiding (foldr,map)
import Control.Arrow hiding ((<+>))

import Utils
import Pretty
import TypeSyn
import DualSyn
import VariableSyn
import DualPrelude (prelude)

type Ctx = [(Variable,Type)]

--------------------------------------------------------------------------------
--                                isType                                      --
--------------------------------------------------------------------------------
{- Checks whether a type is well formed -}

isType :: [Decl]              -- ^ A set of type signatures
       -> [(Variable,Type)] -- ^ A context of bindings of type variables
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
--                            Type Scheme Inference                           --
--------------------------------------------------------------------------------
{-
Citations:
- Lee and Yi. /Proofs about a Folklore Let-Polymorphic Type Inference
  Algorithm/. 1998.
- Odersky, Sulzmann, and Wehr. /Type Inference with Constrained Types/. 1999.
-}

data TypeScheme :: * where
  TyMono   :: Type -> TypeScheme
  TyForall :: Variable -> TypeScheme -> TypeScheme
  deriving Eq

instance Pretty TypeScheme where
  pp (TyMono ty)     = pp ty
  pp (TyForall v ty) = "∀" <> pp v <> "." <+> pp ty

instance Show TypeScheme where
  show = pp

instance FV TypeScheme where
  fvs (TyMono ty)     = fvs ty
  fvs (TyForall v tys) = fvs tys \\ singleton v

{-
The environment and substitution types are closely related. The difference
between the two is that environments map to type-schemes and substitutions map
types.
-}
newtype Env = Env [(Variable,TypeScheme)]

unEnv :: Env -> [(Variable,TypeScheme)]
unEnv (Env e) = e

emptyEnv :: Env
emptyEnv = Env []

instance FV Env where
  fvs (Env []) = empty
  fvs (Env ((_,t):e)) = fvs t `union` fvs (Env e)

instance Monoid Env where
  mempty = Env []
  mappend (Env a) (Env b) = Env (a <> b)

newtype Subst = Subst (Env -> Env)

app :: Subst -> Env -> Env
app = unSubst

unSubst :: Subst -> (Env -> Env)
unSubst (Subst f) = f

idSubst :: Subst
idSubst = undefined

infixr 1 ./.
(./.) :: Type -> Variable -> Subst
t ./. v =
  Subst (  Env
         . fmap (\(v',t') ->
                  case v' == v of
                    True -> (v',t')
                    False -> (v,typeClosure t))
         . unEnv)

infixr 0 ∘
(∘) :: Subst -> Subst -> Subst
(Subst f) ∘ (Subst g) = Subst (f . g)

tsElim :: TypeScheme -> Std Type
tsElim (TyMono ty) = return ty
tsElim (TyForall v ty) =
  do { v' <- TyVar <$> freshVariable
     ; ty' <- tsElim ty
     ; return undefined
     -- ; return (app (Subst [(v,v')]) ty')
     }

tsIntro :: Env -> Type -> TypeScheme
tsIntro e ty = foldr TyForall (TyMono ty) (fvs ty \\ fvs e)

inferTSProgram :: Program Term -> Std TypeScheme
inferTSProgram pgm = undefined
--   = fmap ( typeClosure . fst )
--   $ inferTS ( mkContextTS . pgmDecls $ pgm )
--   $ pgmTerm pgm

-- inferTSTerm :: Term -> Std TypeScheme
-- inferTSTerm = fmap ( typeClosure . fst ) <$> inferTS (mkContextTS prelude)

-- inferTS :: Env -> Term -> Type -> Std Subst
-- inferTS _ (Let _ _ _) = unimplementedErr "inferTS{let}"

-- inferTS c (Ann a ty) =
--   do { (aty,acs) <- inferTS c a
--      ; return (aty, acs <> [(aty,ty)])}

-- inferTS _ (Lit _) = return (TyInt,[])
-- inferTS e (Add a b) =
--   do { (aty,acs) <- inferTS e a
--      ; (bty,bcs) <- inferTS e b
--      ; return (TyInt, acs <> bcs <> [(aty,TyInt),(bty,TyInt)])
--      }

-- inferTS e (Var v) =
--   do { tys <- lookupStd v (unEnv e)
--      ; ty <- tsElim tys
--      ; return (ty,[]) }

-- inferTS e (Fix v t) =
--   do { ty <- TyVar <$> freshVariable
--      ; inferTS (pEnv (v,TyMono ty) <> e) t }

-- inferTS e (App a b) =
--   do { (aty,acs) <- inferTS e a
--      ; (bty,bcs) <- inferTS e b
--      ; retTy <- TyVar <$> freshVariable
--      ; return (retTy, acs <> bcs <> [(aty, TyArr bty retTy)])
--      }

-- inferTS e (Cons k) =
--   do { tys <- lookupStd k (unEnv e)
--      ; ty <- tsElim tys
--      ; return (ty,[]) }

-- inferTS e (Case a _) = inferTS e a

-- inferTS e (Dest h) =
--   do { tys <- lookupStd h (unEnv e)
--      ; ty <- tsElim tys
--      ; return (ty,[]) }

-- inferTS _ (CoCase _) = unimplementedErr "inferTS{cocase}"
-- inferTS e (Prompt a) = inferTS e a

-- inferTSPattern :: Env -> Pattern -> Std Env
-- inferTSPattern e PWild = return e
-- inferTSPattern (Env e) (PVar v) =
--   do { v' <- freshVariable
--      ; return . Env $ e <> [(v,TyForall v' (TyMono (TyVar v')))] }
-- inferTSPattern (Env e) (PCons k _) =
--   do { _ <- lookupStd k e
--      ; unimplementedErr "inferTSPattern" }

-- inferTSCopattern :: Env -> CoPattern -> Std Env
-- inferTSCopattern _ _ = unimplementedErr "inferTSCopattern"

typeClosure :: Type -> TypeScheme
typeClosure ty = foldr (\v -> TyForall v) (TyMono ty) (fvs ty)

occurs :: Variable -> Type -> Bool
occurs _ TyInt       = False
occurs v (TyArr a b) = occurs v a || occurs v b
occurs v (TyVar v')  = v == v'
occurs v (TyCons k)  = v == k
occurs v (TyApp a b) = occurs v a || occurs v b

unify :: Type -> Type -> Std Subst
unify TyInt TyInt = return idSubst

unify (TyArr a b) (TyArr a' b') =
  do { as <- unify a a'
     ; bs <- unify b b'
     ; return (as ∘ bs) }

unify (TyVar v) (TyVar w) =
  case v == w of
    True  -> return idSubst
    False -> unificationErr (TyVar v) (TyVar w)

unify (TyVar v) ty =
  case elem v (fvs ty) of
    True -> unificationErr (TyVar v) ty
    False -> return (ty ./. v)

unify ty (TyVar v) =
  case elem v (fvs ty) of
    True -> unificationErr (TyVar v) ty
    False -> return (ty ./. v)

unify (TyCons k) (TyCons h) =
  case k == h of
    True  -> return idSubst
    False -> unificationErr (TyCons k) (TyCons h)

unify (TyApp a b) (TyApp a' b') =
  do { as <- unify a a'
     ; bs <- unify b b'
     ; return (as ∘ bs) }

unify a b = unificationErr a b

--------------------------------------------------------------------------------
--                              Bidirectional Tc                              --
--------------------------------------------------------------------------------
{- Attempt at a bidirectional typechecker. We do not include declarations in the
~infer~ and ~check~ functions because we populate the Ctx with the necessary
information before running.
-}

typeOfProgram :: Program Term -> Std Type
typeOfProgram (Pgm decls term) = infer (mkContext decls) term

-----------
-- infer --
-----------
infer :: Ctx -> Term -> Std Type
infer c (Let x a b) =
  do { aty <- infer c a
     ; infer ((x,aty):c) b }

infer c (Ann a ty) = check c a ty >> return ty

infer _ (Lit _) = return TyInt

infer c (Add a b) =
  do { check c a TyInt
     ; check c b TyInt
     ; return TyInt }

infer c (Var v) = lookupStd v c
infer c (Fix _ t) = infer c t
infer c (Cons k) = lookupStd k c
infer c (Dest h) = lookupStd h c

infer c (App a b) =
  do { ty <- infer c a
     ; case ty of
         TyArr tyDom tyCod ->
           do { check c b tyDom
              ; return tyCod }
         _ -> typeErr ("must have a function type: " ++ pp a)
     }

infer c (Case e alts) =
  do { ety <- infer c e
     ; tys <- mapM (\(p,u) -> checkPat c p ety >>= \c' -> infer c' u)
                   alts
     ; case tys of
         [] -> typeErr "cannot type empty case"
         (t:ts) ->
           case all (== t) ts of
             True  -> return t
             False -> typeErr "all branches must return the same type."
     }

infer _ (CoCase _) = unimplementedErr "infer{CoCase}"
{- Consider the term
```
  fst { fst □ -> 42 }
```
We must check that the arugment
-}

infer c (Prompt t) = infer c t

inferCopat :: Ctx -> Type -> CoPattern -> Std (Type,Ctx)
inferCopat c ety QHead = return (ety,c)
inferCopat c ety (QDest h q) =
  do { (_,c') <- inferCopat c ety q
     ; _ <- lookupStd h c'
     ; return (TyInt,c') }

inferCopat _ _ (QPat _ _) = unimplementedErr "inferCopat"
inferCopat _ _ (QVar _ _) = unimplementedErr "inferCopat{qvar}"

-----------
-- check --
-----------

check :: Ctx -> Term -> Type -> Std ()
check _ (Let _ _ _) _ = unimplementedErr "check{Let}"
check c (Ann a aty) ty =
  case aty == ty of
    True -> check c a ty
    False -> typeErr ("expected type" <+> pp ty <+> "given" <+> pp aty)
check _ (Lit _) ty =
  case ty == TyInt of
    True -> return ()
    False -> typeErr ("expected type" <+> pp ty <+> "given" <+> pp TyInt)
check c (Add a b) ty =
  case ty == TyInt of
    True -> check c a TyInt >> check c b TyInt
    False -> typeErr ("expected type" <+> pp ty <+> "given" <+> pp TyInt)
check c (Var v) ty =
  do { ty' <- lookupStd v c
     ; case ty == ty' of
         True -> return ()
         False -> typeErr ("expected '" <+> pp v
                           <+> "' to have type" <+> pp ty) }
check c (Fix v t) ty = check ((v,ty):c) t ty
check c (Cons k) ty =
  do { ty' <- lookupStd k c
     ; case ty == ty' of
         True -> return ()
         False -> typeErr ("expected '" <+> pp k
                           <+> "' to have type" <+> pp ty) }
check c (Dest h) ty =
  do { ty' <- lookupStd h c
     ; case ty == ty' of
         True -> return ()
         False -> typeErr ("expected '" <+> pp h
                           <+> "' to have type" <+> pp ty) }
check c (App a b) ty =
  do { aty <- infer c a
     ; case aty of
         TyArr dom cod ->
           case cod == ty of
             True -> check c b dom
             False -> typeErr ("expected '" <+> pp a
                               <+> "' to have return type" <+> pp ty)
         _ -> typeErr ("must have a function type: " ++ pp a)
     }
check c (Case e alts) ty =
  do { ety <- infer c e
     ; alttys <- mapM (\(p,u) -> checkPat c p ety >>= \c' -> infer c' u) alts
     ; case all (== ty) alttys of
         True  -> return ()
         False -> typeErr ("alternatives do not have expected type" <+> pp ty)
     }
check _ (CoCase _) _ = error "check{CoCase}"
check c (Prompt t) ty =
  do { ty' <- infer c t
     ; case ty' == ty of
         True -> return ()
         False -> typeErr ("expected type" <+> pp ty <+> "given" <+> pp ty')
     }

{- checking patterns produces a new context that binds variables of some type.
-}
checkPat :: Ctx -> Pattern -> Type -> Std Ctx
checkPat c PWild        _ = return c
checkPat c (PVar v)     t = return ((v,t):c)
checkPat c (PCons k ps) ty =
  do { kty <- lookupStd k c
     ; case tyCodomain kty == ty of
         True ->
           case length ps == funArity kty of
             True  ->
               do { cs <- mapM (\(ty',p') -> checkPat c p' ty')
                               (zip (collectFunArgTys kty) ps)
                  ; return (mconcat cs <> c) }
             False -> typeErr ("constructor '" <> pp k
                               <> "' has arity" <+> show (funArity kty))
         False -> typeErr (pp k <+> "is not a constructor of type" <+> pp ty)
     }
  where collectFunArgTys :: Type -> [Type]
        collectFunArgTys (TyArr a b) = a : collectFunArgTys b
        collectFunArgTys x = [x]
        tyCodomain :: Type -> Type
        tyCodomain (TyArr _ b) = tyCodomain b
        tyCodomain t = t

--------------------------------------------------------------------------------
--                                 Utils                                      --
--------------------------------------------------------------------------------

mkContext :: [Decl] -> [(Variable,Type)]
mkContext [] = []
mkContext (d:ds) =
  (case d of
     Left neg -> map (\p -> (projName p, projType p))
                    (projections neg)
     Right pos -> map (\i -> (injName i, injType i)) (injections pos)
  ) <> (mkContext ds)

mkContextTS :: [Decl] -> Env
mkContextTS = Env . fmap (second typeClosure) . mkContext

lookupDecl :: Variable -> [Decl] -> Maybe Decl
lookupDecl _ [] = Nothing
lookupDecl v ((Left d):ds) = case v == negTyName d of
                               True -> Just (Left d)
                               False -> lookupDecl v ds
lookupDecl v ((Right d):ds) = case v == posTyName d of
                               True -> Just (Right d)
                               False -> lookupDecl v ds

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
