{-# LANGUAGE GADTs,KindSignatures,UnicodeSyntax #-}
module Judgement where

import Data.Monoid
import Data.Set hiding (foldr,map)
import Control.Arrow hiding ((<+>))
import Control.Monad

import Utils
import Pretty
import TypeSyn
import DualSyn
import VariableSyn

type Ctx = [(Variable,Type)]

--------------------------------------------------------------------------------
--                                isType                                      --
--------------------------------------------------------------------------------
{- Checks whether a type is well formed -}

isType :: [Decl]            -- ^ A set of type signatures
       → [(Variable,Type)] -- ^ A context of bindings of type variables
       → Type
       → Bool
isType _ _   TyInt         = True
isType s ctx (TyArr a b)   = isType s ctx a && isType s ctx b
isType s ctx (TyVar v)     = case lookup v ctx of
                               Just t → isType s ctx t
                               Nothing → False

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
- Damas and Milner. /Principal type-schemes for functional programs/. 1982.
- Lee and Yi. /Proofs about a Folklore Let-Polymorphic Type Inference
  Algorithm/. 1998.
- Odersky, Sulzmann, and Wehr. /Type Inference with Constrained Types/. 1999.
-}

data TypeScheme :: * where
  TyForall :: Set Variable → Type → TypeScheme
  deriving Eq

instance Pretty TypeScheme where
  pp (TyForall vs τ) =
    case size vs == 0 of
      True -> pp τ
      False -> "∀" <+> (smconcat . fmap pp . toList $ vs) <+> "⇒"
                    <+> pp τ

instance Show TypeScheme where
  show = pp

instance FV TypeScheme where
  fvs (TyForall vs τs) = fvs τs \\  vs

arity :: TypeScheme → Int
arity (TyForall _ τ) = funArity τ

codom :: TypeScheme → Type
codom (TyForall _ τ) = codomain τ

{-
The environment and substitution types are closely related. The difference
between the two is that environments map to type-schemes and substitutions map
types.

Environments are finite maps from variables to type schemes.
-}
newtype Env = Env [(Variable,TypeScheme)]
  deriving Show

unEnv :: Env → [(Variable,TypeScheme)]
unEnv (Env e) = e

emptyEnv :: Env
emptyEnv = Env []

extendEnv :: Variable → TypeScheme → Env → Env
extendEnv v s = Env . ((v,s):) . unEnv

instance FV Env where
  fvs (Env []) = empty
  fvs (Env ((_,t):e)) = fvs t `union` fvs (Env e)

instance Monoid Env where
  mempty = Env []
  mappend (Env a) (Env b) = Env (a <> b)

newtype Subst = Subst (Type → Type)

apply :: Subst → Type → Type
apply = unSubst

applyScheme :: Subst → TypeScheme → TypeScheme
applyScheme σ (TyForall vs τ) = TyForall vs (apply σ τ)

applyEnv :: Subst → Env → Env
applyEnv σ = Env . fmap (\(v,s) → (v,applyScheme σ s)) . unEnv

unSubst :: Subst → (Type → Type)
unSubst (Subst f) = f

idSubst :: Subst
idSubst = Subst id

{- Create a subsitution -}
infixr 1 ./.
(./.) :: Type → Variable → Subst
t ./. v =
   Subst (substVar t v)
   where substVar :: Type → Variable → Type → Type
         substVar _ _ TyInt = TyInt
         substVar t' v' (TyArr a b) = TyArr (substVar t' v' a)
                                            (substVar t' v' b)
         substVar t' v' (TyVar v'') =
           case v' == v'' of
             True → t'
             False → TyVar v''
         substVar _ _ (TyCons c) = TyCons c
         substVar t' v' (TyApp a b) = TyApp (substVar t' v' a)
                                            (substVar t' v' b)


{- A composition operation for substitutions. -}
infixr 0 ∘
(∘) :: Subst → Subst → Subst
(Subst f) ∘ (Subst g) = Subst (f . g)

tsElim :: TypeScheme → Std Type
tsElim (TyForall vs τ) =
  foldM (\τ' v →
            do { α ← TyVar <$> freshen v
               ; return (apply (α ./. v) τ') })
         τ
        (toList vs)

typeClosure :: Env → Type → TypeScheme
typeClosure e τ = TyForall (fvs τ \\ fvs e) τ

{- Top level -}
inferTSProgram :: Program Term → Std TypeScheme
inferTSProgram pgm =
  do { τ ← TyVar <$> freshVariable
     ; s ← inferTS ( mkContextTS . pgmDecls $ pgm )
                    ( pgmTerm pgm )
                    τ
     ; return . typeClosure emptyEnv . apply s $ τ }

inferTS :: Env → Term → Type → Std Subst
inferTS e (Let v a b) ρ =
  do { α  ← TyVar <$> freshVariable
     ; sa ← inferTS e a α
     ; let e' = extendEnv v (typeClosure e (apply sa α)) (applyEnv sa e)
     ; sb ← inferTS e' b (apply sa ρ)
     ; return (sb ∘ sa)
     }

inferTS e (Ann a τ) ρ =
  do { sa ← inferTS e a τ
     ; unify τ (apply sa ρ)
     }

inferTS _ (Lit _) ρ = unify ρ TyInt

inferTS e (Add a b) ρ =
  do { sa ← inferTS e a TyInt
     ; sb ← inferTS (applyEnv sa e) b TyInt
     ; unify TyInt (apply (sb ∘ sa) ρ)
     }

inferTS e (Var v) ρ = unify ρ =<< tsElim =<< lookupStd v (unEnv e)

inferTS e (Fix v t) ρ =
  do { τ ← TyVar <$> freshVariable
     ; let e' = extendEnv v (typeClosure e τ) e
     ; st ← inferTS e' t ρ
     ; return st
     }

inferTS e (App a b) ρ =
  do { β ← TyVar <$> freshVariable
     ; sa ← inferTS e a (TyArr β ρ)
     ; sb ← inferTS (applyEnv sa e) b (apply sa β)
     ; return (sb ∘ sa)
     }

inferTS e (Cons k) ρ = unify ρ =<< tsElim =<< lookupStd k (unEnv e)

inferTS e (Case t alts) ρ =
  do { τ ← TyVar <$> freshVariable
     ; st ← inferTS e t τ
     ; salts ← forM alts $ \(p,u) →
         do { e' ← inferTSPattern (applyEnv st e) p τ
            ; inferTS e' u ρ }
     ; return (foldr (∘) st salts)
     }

inferTS e (Dest h) ρ = unify ρ =<< tsElim =<< lookupStd h (unEnv e)

inferTS e (CoCase coalts) ρ =
  do { scoalts ← forM coalts $ \(q,u) →
         do { e' ← inferTSCopattern e q ρ
            ; inferTS e' u ρ }
     ; return (foldr (∘) idSubst scoalts)
     }

inferTS _ (Prompt _) _ = unimplementedErr "inferTS{prompt}"

inferTSPattern :: Env → Pattern → Type → Std Env
inferTSPattern e PWild _ = return e
inferTSPattern e (PVar v) ρ = return (extendEnv v (typeClosure e ρ) e)
inferTSPattern e (PCons k ps) ρ =
  do { α ← tsElim =<< lookupStd k (unEnv e)
     ; foldPList e ps α
     }
  where foldPList :: Env → [Pattern] → Type → Std Env
        foldPList e (p:ps) (TyArr a b) =
          do { e' ← inferTSPattern e p a
             ; foldPList e' ps b }
        foldPList _ [] (TyArr _ _) =
          typeErr "incorrect number of arguments in pattern"
        foldPList e [] _ = return e

inferTSCopattern :: Env → CoPattern → Type → Std Env
inferTSCopattern e QHead _ = return e
inferTSCopattern e (QDest h q) ρ =
  do { δ ← tsElim =<< lookupStd h (unEnv e)
     ; e' ← inferTSCopattern e q δ
     ; return e'
     }
inferTSCopattern _ (QPat _ _) _ = unimplementedErr "inferTSCopattern{qpat}"

occurs :: Variable → Type → Bool
occurs _ TyInt       = False
occurs v (TyArr a b) = occurs v a || occurs v b
occurs v (TyVar v')  = v == v'
occurs v (TyCons k)  = v == k
occurs v (TyApp a b) = occurs v a || occurs v b

unify :: Type → Type → Std Subst
unify TyInt TyInt = return idSubst

unify (TyArr a b) (TyArr a' b') =
  do { as ← unify a a'
     ; bs ← unify b b'
     ; return (bs ∘ as) }

unify (TyVar v) ty =
  case elem v (fvs ty) of
    True → unificationErr (TyVar v) ty
    False → return (ty ./. v)

unify ty (TyVar v) =
  case elem v (fvs ty) of
    True → unificationErr (TyVar v) ty
    False → return (ty ./. v)

unify (TyCons k) (TyCons h) =
  case k == h of
    True  → return idSubst
    False → unificationErr (TyCons k) (TyCons h)

unify (TyApp a b) (TyApp a' b') =
  do { as ← unify a a'
     ; bs ← unify b b'
     ; return (bs ∘ as) }

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
     Left neg -> map (arr projName &&& arr projType)
                    (projections neg)
     Right pos -> map (arr injName &&& arr injType) (injections pos)
  ) <> (mkContext ds)

mkContextTS :: [Decl] -> Env
mkContextTS = Env . fmap (second (typeClosure emptyEnv)) . mkContext

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
