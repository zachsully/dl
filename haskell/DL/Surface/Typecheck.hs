module DL.Surface.Typecheck
  ( TcConfig (..)
  , typeCheckPgm
  ) where

import Control.Monad
import Data.Map.Lazy hiding (foldr)
import qualified Data.Set as Set

import DL.Surface.Syntax
import DL.General.Type
import DL.General.Top
import DL.General.Variable
import DL.Utils.StdMonad
import DL.Utils.Pretty

--------------------------------------------------------------------------------
--                            Environments                                    --
--------------------------------------------------------------------------------
newtype Env a = Env (Map Variable a)

emptyEnv :: Env a
emptyEnv = Env empty

extendEnv :: Variable -> a -> Env a -> Env a
extendEnv v a (Env m) = Env (insert v a m)

lookupEnv :: Variable -> Env a -> Tc a
lookupEnv v (Env m) =
  case Data.Map.Lazy.lookup v m of
    Nothing -> typeError (UnboundVarError v)
    Just a  -> return a

instance FV a => FV (Env a) where
  fvs (Env m) = Set.unions . fmap fvs . elems $ m

-- | forall introduction, we only generalize constructors and destructors
generalize :: Env Scheme -> Maybe Constraint -> Type -> Scheme
generalize _ Nothing ty = Forall (fvs ty) mempty ty
generalize _ (Just c) ty = Forall (Set.union (fvs ty) (fvs c)) c ty

-- | forall elimination
instantiate :: Scheme -> Tc (Type,Constraint)
instantiate (Forall vs c ty) =
  do { s <- foldM (\s v ->
                     do { fTy <- freshTy
                        ; return (replace v fTy . s) })
                  id
                  (Set.toList vs)
     ; return (s ty,applyConstraint s c) }

--------------------------------------------------------------------------------
--                          Typechecking Monad                                --
--------------------------------------------------------------------------------
data TcState = TcState { freshNames :: [Type] }

initTcState :: TcState
initTcState
  = TcState (zipWith (\l r -> TyVar (Variable (l++show r)))
                     (repeat "t")
                     [(0 :: Integer)..])

-- | The typechecking monad is a state monad that can fail
data Tc a = Tc { unTc :: TcState -> Either TypeError (TcState,a) }

instance Functor Tc where
  fmap = liftM

instance Applicative Tc where
  pure = return
  (<*>) = ap

instance Monad Tc where
  return x = Tc $ \s -> Right (s,x)
  (Tc m) >>= g = Tc $ \s ->
    case m s of
      Left e -> Left e
      Right (s',x) -> unTc (g x) s'

typeError :: TypeError -> Tc a
typeError e = Tc (\_ -> Left e)

freshTy :: Tc Type
freshTy = Tc $ \s ->
  let (x:xs) = freshNames s in
    Right (s { freshNames = xs },x)

--------------------------------------------------------------------------------
--                           Constraint Solver                                --
--------------------------------------------------------------------------------

type Subst = Type -> Type

replace :: Variable -> Type -> Subst
replace _ _ TyInt = TyInt
replace v ty (TyArr a b) =
  TyArr (replace v ty a) (replace v ty b)
replace v ty (TyVar w) =
  case v == w of
    True  -> ty
    False -> TyVar w
replace _ _ (TyCons k) = TyCons k
replace v ty (TyApp a b) =
  TyApp (replace v ty a) (replace v ty b)

unify :: Type -> Type -> Tc Subst
unify a b | a == b = return id
unify (TyArr a b) (TyArr c d) =
  do { s1 <- unify a c
     ; s2 <- unify (s1 b) (s1 d)
     ; return (s2 . s1) }
unify (TyVar v) b =
  case occurs v b of
    True  -> typeError (InfiniteTypeError v b)
    False -> return (replace v b)
unify a (TyVar v) =
  case occurs v a of
    True  -> typeError (InfiniteTypeError v a)
    False -> return (replace v a)
unify (TyCons k) (TyCons h) =
  case k == h of
    True  -> return id
    False -> typeError (UnificationError (TyCons k) (TyCons h))
unify (TyApp a b) (TyApp c d) =
  do { s1 <- unify a c
     ; s2 <- unify (s1 b) (s1 d)
     ; return (s2 . s1) }
unify a b = typeError (UnificationError a b)

occurs :: Variable -> Type -> Bool
occurs v a = elem v (fvs a)

solve :: Subst -> Constraint -> Tc Subst
solve s CTrue = return s
solve s c =
  do { (c',s') <- solve' (applyConstraint s c)
     ; solve (s' . s) c' }

solve' :: Constraint -> Tc (Constraint,Subst)
solve' CTrue = return (mempty,id)
solve' (CConj CTrue c) = solve' c
solve' (CConj c CTrue) = solve' c
solve' (CConj a b) =
  do { (aC,aS) <- solve' a
     ; (bC,bS) <- solve' (applyConstraint aS b)
     ; return (applyConstraint (bS . aS) (aC <> bC),bS . aS) }
solve' (CNumeric TyInt) = return (mempty, id)
solve' (CNumeric ty) = typeError (UnificationError ty TyInt)
solve' (CEq a b) | a == b = return (mempty, id)
solve' (CEq a b) =
  do { s <- unify a b
     ; return (mempty, s) }

applyConstraint :: Subst -> Constraint -> Constraint
applyConstraint _ CTrue = CTrue
applyConstraint s (CConj a b) = CConj (applyConstraint s a) (applyConstraint s b)
applyConstraint s (CEq a b) = CEq (s a) (s b)
applyConstraint s (CNumeric a) = CNumeric (s a)

--------------------------------------------------------------------------------
--                             Top Level                                      --
--------------------------------------------------------------------------------

data TcConfig
  = TcConfig { tcDumpConstraints :: Bool }

typeCheckPgm :: TcConfig -> Program Term -> IO (Either String Type)
typeCheckPgm cfg (Pgm decls term _) =
  case unTc m initTcState of
    Left e -> return (Left (pp e))
    Right (tcState',(ty,constraint)) ->
      let unsolved = Forall (Set.union (fvs constraint) (fvs ty)) constraint ty
      in when (tcDumpConstraints cfg) (pprint unsolved >> putStrLn "") >>
         case unTc (solveAndApp ty constraint) tcState' of
           Left e -> return (Left (pp e))
           Right (_,ty') -> return (Right ty')
  where m = do { (_,tenv) <- foldM runCheck (emptyEnv,emptyEnv) decls
               ; gatherTerm tenv term }
        solveAndApp ty constraint = solve id constraint <*> pure ty
        runCheck (kenv,Env tm) decl =
          do { (kenv',Env tm') <- gatherDecl kenv decl
             ; return (kenv',Env (union tm tm')) }

-- | Check that a delaration is well formed and add that to the typechecking
-- state
gatherDecl :: Env Kind -> Decl -> Tc (Env Kind,Env Scheme)
gatherDecl kenv (CodataDecl (NegTyCons name fs projs)) =
  do { tenv <- foldM checkProjection emptyEnv projs
     ; return (kenv', tenv) }
  where kind :: Kind
        kind = Kind (length fs)
        kenv' :: Env Kind
        kenv' = extendEnv name kind kenv
        checkProjection :: Env Scheme -> Projection -> Tc (Env Scheme)
        checkProjection tenv (Proj pname mc ty) =
          let expectedTy = Prelude.foldl TyApp (TyCons name) (fmap TyVar fs)
          in do { kindCheckType kenv' ty
                ; case domain ty of
                    Nothing  ->
                      typeError (DestructorProjectionError pname expectedTy)
                    Just dom ->
                      case expectedTy == dom of
                        True ->
                          let tyS = generalize tenv mc ty
                          in return (extendEnv pname tyS tenv)
                        False ->
                          typeError (DestructorProjectionError pname expectedTy)
                }
gatherDecl kenv (DataDecl (PosTyCons name fs injs)) =
  do { tenv <- foldM checkInjection emptyEnv injs
     ; return (kenv', tenv) }
  where kind :: Kind
        kind = Kind (length fs)
        kenv' :: Env Kind
        kenv' = extendEnv name kind kenv
        checkInjection :: Env Scheme -> Injection -> Tc (Env Scheme)
        checkInjection tenv (Inj iname mc ty) =
          let expectedTy = Prelude.foldl TyApp (TyCons name) (fmap TyVar fs)
          in do { kindCheckType kenv' ty
                ; case codomain ty of
                    Nothing  ->
                      case expectedTy == ty of
                        True  ->
                          let tyS = generalize tenv mc ty
                          in return (extendEnv iname tyS tenv)
                        False ->
                          typeError (ConstructorInjectionError iname expectedTy)
                    Just cod ->
                      case expectedTy == cod of
                        True  ->
                          let tyS = generalize tenv mc ty
                          in return (extendEnv iname tyS tenv)
                        False ->
                          typeError (ConstructorInjectionError iname expectedTy)
                }
gatherDecl kenv (IndexDecl name vs)
  = return (extendEnv name (Kind (length vs)) kenv, emptyEnv)

kindCheckType :: Env Kind -> Type -> Tc ()
kindCheckType e ty = kindCheckType' e ty 0

kindCheckType' :: Env Kind -> Type -> Int -> Tc ()
kindCheckType' _ TyInt 0 = return ()
kindCheckType' e (TyArr a b) 0 = kindCheckType e a >> kindCheckType e b
kindCheckType' _ (TyVar _) 0 = return ()
kindCheckType' e (TyCons v) n =
  lookupEnv v e >>= \(Kind k) ->
    case k == n of
      True  -> return ()
      False -> typeError (KindError (TyCons v) (Kind n) (Just (Kind k)))
kindCheckType' e (TyApp a b) n = kindCheckType' e a (n+1) >> kindCheckType e b
kindCheckType' _ ty n = typeError (KindError ty (Kind n) Nothing)


--------------------------------------------------------------------------------
--                       Gather Constraints from Terms                        --
--------------------------------------------------------------------------------

gatherTerm :: Env Scheme -> Term -> Tc (Type,Constraint)
gatherTerm env (Let v a b) =
  do { (aTy,aC) <- gatherTerm env a
     ; (bTy,bC) <- gatherTerm (extendEnv v (Forall Set.empty mempty aTy) env) b
     ; return (bTy, aC <> bC) }
gatherTerm env (Ann a ty) =
  do { (aTy, aC) <- gatherTerm env a
     ; return (aTy, aC <> (aTy `ceq` ty)) }
gatherTerm _   (Lit _) = return (TyInt,mempty)
gatherTerm env (Add a b) =
  do { (aTy,aC) <- gatherTerm env a
     ; (bTy,bC) <- gatherTerm env b
     ; return (TyInt
              , aC <> bC <> (aTy `ceq` TyInt) <> (bTy `ceq` TyInt))
     }
gatherTerm env (Var v) = instantiate =<< lookupEnv v env
gatherTerm env (Fix v a) =
  do { ty <- freshTy
     ; gatherTerm (extendEnv v (generalize env Nothing ty) env) a }
gatherTerm env (App a b) =
  do { (aTy,aC) <- gatherTerm env a
     ; (bTy,bC) <- gatherTerm env b
     ; outTy <- freshTy
     ; return (outTy,aC <>  bC <> (aTy `ceq` (TyArr bTy outTy))) }
gatherTerm env (Cons k) = instantiate =<< lookupEnv k env
gatherTerm env (Case t alts) =
  do { (tTy,tC) <- gatherTerm env t
     ; outTy <- freshTy
     ; cs <- mapM (gatherAlt env tTy outTy) alts
     ; return (outTy, tC <> mconcat cs) }
gatherTerm env (Dest h) = instantiate =<< lookupEnv h env
gatherTerm env (Coalts coalts) =
  do { codataTy <- freshTy
     ; cs <- mapM (gatherCoalt env codataTy) coalts
     ; return (codataTy, mconcat cs) }
gatherTerm env (Cocase o a) =
  do { (aTy,aC) <- gatherTerm env a
     ; (obsTy,obsC) <- gatherObsCtx env aTy o
     ; return (obsTy,obsC <> aC) }
gatherTerm env (StreamCoiter (x,a) (y,b) c) =
  do { (cTy,cC) <- gatherTerm env c
     ; (aTy,aC) <- gatherTerm (extendEnv x (Forall Set.empty mempty cTy) env) a
     ; (bTy,bC) <- gatherTerm (extendEnv y (Forall Set.empty mempty cTy) env) b
     ; return (TyApp (TyCons (Variable "Stream")) aTy
              , cC <> aC <> bC <> (cTy `ceq` bTy)) }
gatherTerm env (Prompt a) = gatherTerm env a

-- | Takes the argument type, the output type, and an alternative and generates
-- a constraint
gatherAlt :: Env Scheme -> Type -> Type -> (Pattern,Term) -> Tc Constraint
gatherAlt env argTy outTy (p,t) =
  do { (env',pC) <- gatherPattern env argTy p
     ; (tTy,tC) <- gatherTerm env' t
     ; return (pC <> tC <> (outTy `ceq` tTy)) }

gatherPattern :: Env Scheme -> Type -> Pattern -> Tc (Env Scheme,Constraint)
gatherPattern env _ PWild = return (env,mempty)
gatherPattern env argTy (PVar v)
  = return (extendEnv v (Forall mempty mempty argTy) env,mempty)
gatherPattern env argTy (PCons k pats) =
  do { kS <- lookupEnv k env
     ; (kTy,kC) <- instantiate kS
     ; (env',pC) <- foldPatterns env kTy pats
     ; return (env', kC <> pC )}
  where foldPatterns e ty@(TyApp _ _) [] = return (e,argTy `ceq` ty)
        foldPatterns e ty@(TyCons _)  [] = return (e,argTy `ceq` ty)
        foldPatterns e ty@(TyVar _)   [] = return (e,argTy `ceq` ty)
        foldPatterns e (TyArr a b) (p:ps) =
          do { (e',pC) <- gatherPattern e a p
             ; (e'',psC) <- foldPatterns e' b ps
             ; return (e'',pC <> psC) }
        foldPatterns _ _ _ = typeError (Unimplemented "foldPatterns")

gatherObsCtx :: Env Scheme -> Type -> ObsCtx -> Tc (Type,Constraint)
gatherObsCtx _ codataTy ObsHead = return (codataTy,mempty)
gatherObsCtx env codataTy (ObsFun o a) =
  do { (obsTy,obsC) <- gatherObsCtx env codataTy o
     ; (aTy, aC) <- gatherTerm env a
     ; outTy <- freshTy
     ; return (outTy, obsC <> aC <> (obsTy `ceq` (TyArr aTy outTy))) }
gatherObsCtx env codataTy (ObsDest h o) =
  do { (obsTy,obsC) <- gatherObsCtx env codataTy o
     ; (hTy,hC) <- instantiate =<< lookupEnv h env
     ; outTy <- freshTy
     ; return (outTy, obsC <> hC <> (hTy `ceq` (TyArr obsTy outTy))) }
gatherObsCtx _ _ (ObsCut _ _) = typeError (Unimplemented "gatherObsCtx{ObsCut}")

-- ^ Takes a codata type, returns the output type
gatherCoalt :: Env Scheme -> Type -> (CoPattern,Term) -> Tc Constraint
gatherCoalt env codataTy (q,t) =
  do { (projTy,qC,env') <- gatherCopattern env codataTy q
     ; (tTy, tC) <- gatherTerm env' t
     ; return (tC <> qC <> (projTy `ceq` tTy)) }

-- ^ Takes the type of the context, returns the type of the projection
gatherCopattern
  :: Env Scheme -> Type -> CoPattern -> Tc (Type,Constraint, Env Scheme)
gatherCopattern env codataTy QHead = return (codataTy,mempty,env)
gatherCopattern env codataTy (QDest h q) =
  do { (projTy,qC,env') <- gatherCopattern env codataTy q
     ; (hTy,hC) <- instantiate =<< lookupEnv h env
     ; outTy <- freshTy
     ; return (outTy, qC <> hC <> (hTy `ceq` (TyArr projTy outTy)), env') }
gatherCopattern env codataTy (QPat q p) =
  do { (projTy,qC,env') <- gatherCopattern env codataTy q
     ; domTy <- freshTy
     ; (env'',pC) <- gatherPattern env' domTy p
     ; outTy <- freshTy
     ; return (outTy, qC <> pC <> (projTy `ceq` (TyArr domTy outTy)), env'') }
gatherCopattern _ _ (QVar _ _) = typeError (Unimplemented "gatherCopattern{QVar}")
gatherCopattern env _ QWild =
  do { outTy <- freshTy
     ; return (outTy,mempty,env) }

--------------------------------------------------------------------------------
--                             Type Errors                                    --
--------------------------------------------------------------------------------
data TypeError
  = InfiniteTypeError Variable Type
  | UnificationError Type Type
  | KindError Type Kind (Maybe Kind)
  | DestructorProjectionError Variable Type
  | ConstructorInjectionError Variable Type
  | UnboundVarError Variable
  | Unimplemented String

instance Pretty TypeError where
  pp te = mkRed "<static error>\n" <> ppTypeError te <> "\n"

ppTypeError :: TypeError -> String
ppTypeError (InfiniteTypeError v ty) =
  "Cannot construct infinite type:" <+> pp v <+> "=" <+> pp ty
ppTypeError (UnificationError a b) =
  "Unable to unify" <+> quasiquotes (pp a) <+> "with" <+> quasiquotes (pp b)
ppTypeError (KindError ty i _) =
  "Type" <+> pp ty <+> "does not have kind" <+> pp i
ppTypeError (DestructorProjectionError h ty) =
  "Destructor" <+> quasiquotes (pp h) <+> "must be a projection from type"
  <+> quasiquotes (pp ty)
ppTypeError (ConstructorInjectionError k ty) =
  "Constructor" <+> quasiquotes (pp k) <+> "must be a injection into type"
  <+> quasiquotes (pp ty)
ppTypeError (UnboundVarError v) =
  "Unbound variable" <+> quasiquotes (pp v)
ppTypeError (Unimplemented s) =
  "Unimplemented:" <+> s
