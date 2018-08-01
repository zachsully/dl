{-# LANGUAGE GADTs,KindSignatures,UnicodeSyntax #-}
module DL.Judgement where

import Data.Monoid
import Data.Set hiding (foldr,map)
import Control.Arrow hiding ((<+>))
import Control.Monad

import DL.Utils
import DL.Pretty
import DL.Syntax.Type
import DL.Syntax.Term
import DL.Syntax.Top
import DL.Syntax.Variable

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

schemeArity :: TypeScheme -> Int
schemeArity (TyForall _ τ) = arity τ

applyScheme :: Subst → TypeScheme → TypeScheme
applyScheme σ (TyForall vs τ) = TyForall vs (applyType σ τ)

codomainTS :: TypeScheme → Maybe Type
codomainTS (TyForall _ τ) = codomain τ

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

applyEnv :: Subst → Env → Env
applyEnv σ = Env . fmap (\(v,s) → (v,applyScheme σ s)) . unEnv

instance Semigroup Env

instance Monoid Env where
  mempty = Env []
  mappend (Env a) (Env b) = Env (a <> b)


{-
Substitutions map types to types. This actually maps type variables within types
to types.
-}
data Subst = Subst { unSubst :: Type → Type }

applyType :: Subst → Type → Type
applyType = unSubst

idSubst :: Subst
idSubst = Subst id

{- Create a subsitution -}
infixr 1 ./.
(./.) :: Type → Variable → Subst
t ./. v = Subst (substVar t v)
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

{- Other helpers -}
tsElim :: TypeScheme → Std Type
tsElim (TyForall vs τ) =
  foldM (\τ' v →
            do { α ← TyVar <$> freshen v
               ; return (applyType (α ./. v) τ') })
         τ
        (toList vs)

typeClosure :: Env → Type → TypeScheme
typeClosure e τ = TyForall (fvs τ \\ fvs e) τ

newTyVar :: Std Type
newTyVar = TyVar <$> freshVariable

{-
The top level inference creates an environment filled with binds which will be
used for construction, observation, and the creation of (co)patterns.

It then obtains a substituion by running ~inferTS~ and applies that to a top
level variable to return the final type scheme of the program.
-}
inferTSProgram :: Program Term → Std TypeScheme
inferTSProgram pgm =
  do { τ ← newTyVar
     ; s ← inferTS ( mkContextTS . pgmDecls $ pgm )
                    ( pgmTerm pgm )
                    τ
     ; return . typeClosure emptyEnv . applyType s $ τ }

{-
~inferTS~ uses a modified version of algorithm M presented by Lee and Yi. The
type argument ~ρ~ is type information propagated down from the root. Instead of
generating a type and substitution as a result as in algorithm W (Damas and
Milner), algorithm M constrains the type as an argument. We use unification to
check that our type satisfies the constraint /and/ to create substitutions.
-}
inferTS :: Env → Term → Type → Std Subst
inferTS e (Let v a b) ρ =
  do { α  ← newTyVar
     ; sa ← inferTS e a α
     ; sb ← inferTS (applyEnv sa (extendEnv v (typeClosure e α) e))
                     b
                     (applyType sa ρ)
     ; return (sb ∘ sa) }

inferTS e (Ann a τ) ρ =
  do { sa ← inferTS e a τ
     ; unify τ (applyType sa ρ) }

inferTS _ (Lit _) ρ = unify ρ TyInt

inferTS e (Add a b) ρ =
  do { sa ← inferTS e a TyInt
     ; sb ← inferTS (applyEnv sa e) b TyInt
     ; unify (applyType (sb ∘ sa) ρ) TyInt  }

inferTS e (Var v) ρ = unify ρ =<< tsElim =<< lookupStd v (unEnv e)

inferTS e (Fix v t) ρ = inferTS (extendEnv v (typeClosure e ρ) e) t ρ

inferTS e (App a b) ρ =
  do { β ← newTyVar
     ; sa ← inferTS e a (TyArr β ρ)
     ; sb ← inferTS (applyEnv sa e) b (applyType sa β)
     ; return (sb ∘ sa) }

inferTS e (Cons k) ρ = unify ρ =<< tsElim =<< lookupStd k (unEnv e)

inferTS e (Case t alts) ρ =
  do { τ ← newTyVar
     ; st ← inferTS e t τ
     ; salts ← mapM (\(p,u) → inferTSAlt (applyEnv st e)
                      p u (applyType st τ) (applyType st ρ))
                     alts
     ; unify ρ (applyType (foldr (∘) st salts) ρ)
     }

inferTS e (Dest h) ρ = unify ρ =<< tsElim =<< lookupStd h (unEnv e)

inferTS _ (Cocase _ _) _ = unimplementedErr "inferTS{cocase}"
{- Cocase inference:
We must be able to unify the types of all the branches of a cocase, e.g.
{ Head [□ x] → x ; Tail [□ x] → nats } both branches must unify to ~Stream Int~.
The judgement of the types is actually done by coalternative inference.
-}
inferTS e (Coalts coalts) _ =
  do { vs ← replicateM (length coalts) (TyVar <$> freshVariable)
     ; _ ← mapM (\(v,(q,u)) → inferTSCoalt e q u v) (zip vs coalts)
     ; unimplementedErr "inferTS{coalts}"
     -- ; foldM (unify ρ) idSubst scoalts
     }

inferTS _ (Prompt _) _ = unimplementedErr "inferTS{prompt}"

{-
The first of the type arguments describes the type of the interrogated term.
The second of the type arguments describes the output type of the alternative
statement.
-}
inferTSAlt :: Env → Pattern → Term → Type → Type → Std Subst
inferTSAlt e p u τ σ =
  do { (e',sp) ← inferTSPattern e p τ
     ; inferTS (applyEnv sp e') u (applyType sp σ) }

inferTSPattern :: Env → Pattern → Type → Std (Env,Subst)
inferTSPattern e PWild _ = return (e,idSubst)
inferTSPattern e (PVar v) ρ = return (extendEnv v (typeClosure e ρ) e, idSubst)
inferTSPattern e (PCons k ps) _ =
  do { κ ← tsElim =<< lookupStd k (unEnv e)
     ; case length ps == arity κ of
         False → typeErr ("constructor" <+> pp k <+> "requires"
                          <+> show (arity κ) <+> "arguments")
         True →
           case collectTyArgs κ of
             Just (_,args) →
               do { _ ← mapM (\(τ,p) → inferTSPattern e p τ) (zip args ps)
                  ; unimplementedErr "inferTSPattern{PCons}" }
             Nothing → typeErr "pattern not constructor"
     }

{-
Unlike infering the type of an alternative, coalternatives do not necessarily
have an interrogated term.
-}
inferTSCoalt :: Env → CoPattern → Term → Type → Std Subst
inferTSCoalt e q u ρ =
  do { (e',sq) ← inferTSCopattern e q ρ
     ; inferTS (applyEnv sq e') u (applyType sq ρ) }

inferTSCopattern :: Env → CoPattern → Type → Std (Env,Subst)
inferTSCopattern e QHead _ = return (e,idSubst)
inferTSCopattern e (QDest h q) ρ =
  do { _ ← tsElim =<< lookupStd h (unEnv e)
     ; (_,_) ← inferTSCopattern e q ρ
     ; unimplementedErr "inferTSCopattern{qdest}" }

inferTSCopattern e (QPat q p) ρ =
  do { σ ← newTyVar
     ; ε ← newTyVar
     ; (e',s) ← inferTSPattern e p σ
     ; (e'',s') ← inferTSCopattern e' q (applyType s ε)
     ; s'' ← unify ρ (applyType s' (TyArr σ ε))
     ; return (e'', s'') }
inferTSCopattern _ _ _ = unimplementedErr "inferTSCopattern{qvar}"

{-
Type unification, this is standard (i.e. unmodified from other unification
algorithms).
-}
unify :: Type → Type → Std Subst
unify TyInt TyInt = return idSubst

unify (TyArr a b) (TyArr a' b') =
  do { as ← unify a a'
     ; bs ← unify b b'
     ; return (bs ∘ as) }

unify (TyVar v) τ =
  case occurs v τ of
    True → unificationErr (TyVar v) τ
    False → return (τ ./. v)

unify τ (TyVar v) =
  case occurs v τ of
    True → unificationErr (TyVar v) τ
    False → return (τ ./. v)

unify (TyCons k) (TyCons h) =
  case k == h of
    True  → return idSubst
    False → unificationErr (TyCons k) (TyCons h)

unify (TyApp a b) (TyApp a' b') =
  do { as ← unify a a'
     ; bs ← unify b b'
     ; return (bs ∘ as) }

unify α β = unificationErr α β

occurs :: Variable → Type → Bool
occurs v τ = elem v (fvs τ)

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

infer _ (Cocase _ _) = unimplementedErr "infer{Cocase}"
infer _ (Coalts _) = unimplementedErr "infer{Coalts}"
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
check _ (Coalts _) _ = error "check{Coalts}"
check _ (Cocase _ _) _ = error "check{Cocase}"
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
           case length ps == arity kty of
             True  ->
               do { cs <- mapM (\(ty',p') -> checkPat c p' ty')
                               (zip (collectFunArgTys kty) ps)
                  ; return (mconcat cs <> c) }
             False -> typeErr ("constructor '" <> pp k
                               <> "' has arity" <+> show (arity kty))
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
     (Decl (Left neg)) -> map (arr projName &&& arr projType)
                    (projections neg)
     (Decl (Right pos)) -> map (arr injName &&& arr injType) (injections pos)
  ) <> (mkContext ds)

mkContextTS :: [Decl] -> Env
mkContextTS = Env . fmap (second (typeClosure emptyEnv)) . mkContext

lookupDecl :: Variable -> [Decl] -> Maybe Decl
lookupDecl _ [] = Nothing
lookupDecl v (Decl (Left d):ds) =
  case v == negTyName d of
    True -> Just . mkCodataDecl $ d
    False -> lookupDecl v ds
lookupDecl v (Decl (Right d):ds) =
  case v == posTyName d of
    True -> Just . mkDataDecl $ d
    False -> lookupDecl v ds

lookupDatum :: Variable -> [Decl] -> Maybe Decl
lookupDatum _ [] = Nothing
lookupDatum h (Decl (Left  d):ds) =
  case lookupProjection h (projections d) of
    Just _ -> Just . mkCodataDecl $ d
    Nothing -> lookupDatum h ds
lookupDatum k (Decl (Right d):ds) =
  case lookupInjection k (injections d) of
    Just _ -> Just . mkDataDecl $ d
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
