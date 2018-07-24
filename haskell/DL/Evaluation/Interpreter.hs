{-# LANGUAGE
      DataKinds,
      GADTs,
      KindSignatures,
      TypeFamilies,
      UnicodeSyntax
#-}
module DL.Evaluation.Interpreter where

import Data.Monoid
import DL.Utils
import DL.Pretty
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Evaluation.Strategy
import Debug.Trace

data Val :: Strategy -> * where
  VTerm     :: FlatTerm -> Val CallByName
  VLit      :: Int -> Val s
  VConsVal  :: Variable -> [Val CallByValue] -> Val CallByValue
  VConsTerm :: Variable -> [FlatTerm] -> Val CallByName
  VFun      :: Variable -> FlatTerm -> Val s
  VCoalt    :: (Variable,FlatTerm) -> FlatTerm -> Val s
  VEmpty    :: Val s

instance Eq (Val s) where
  (VTerm a)       == (VTerm b)  = a == b
  (VLit i)        == (VLit j)   = i == j
  (VConsVal k vs) == (VConsVal j ws) = k == j && vs == ws

instance Show (Val s) where
  show (VTerm t) = show t

instance Pretty (Val s) where
  pp (VTerm t) = pp t

data EvalCtx :: Strategy -> * where
  EEmpty   :: EvalCtx s
  EPrompt  :: EvalCtx s -> EvalCtx s
  EAddL    :: EnvCBN    -> EvalCtx s -> FlatTerm  -> EvalCtx s
  EAddR    :: Int       -> EvalCtx s -> EvalCtx s
  ECase    :: EvalCtx s -> (FlatPattern,FlatTerm) -> (Variable,FlatTerm)
           -> EvalCtx s
  EAppFun  :: EvalCtx s -> FlatTerm -> EvalCtx s
  EAppDest :: Variable  -> EvalCtx s -> EvalCtx s
  EAppArg  :: (cbv ~ CallByValue) => Val cbv -> EvalCtx cbv -> EvalCtx cbv

instance Eq (EvalCtx s) where
  EEmpty == EEmpty = True
  (EPrompt a)    == (EPrompt b)    = a == b
  (EAddL e a t)  == (EAddL e' b u) = e == e' && a == b && t == u
  (EAddR v a)    == (EAddR w b)    = a == b && v == w
  (ECase e a b)  == (ECase f c d)  = e == f && a == c && b == d
  (EAppFun a t)  == (EAppFun b e)  = a == b && t == e
  (EAppDest v a) == (EAppDest w b) = a == b && v == w
  (EAppArg v a)  == (EAppArg w b)  = a == b && v == w
  _ == _ = False

instance Show (EvalCtx s) where
  show EEmpty = "#"
  show (EPrompt t) = "#" <+> show t
  show (EAddL e k t) = show e <+> show k <+> "+" <+> show t
  show (EAddR i e) = show i <+> "+" <+> show e
  show (ECase e a b) = "case" <+> show e <+> show a <+> "|" <+> show b
  show (EAppFun e t) = show e <+> show t
  show (EAppDest h e) = show h <+> show e
  show (EAppArg v e) = undefined

instance Pretty (EvalCtx s) where
  pp EEmpty = "#"
  pp (EPrompt t) = "#" <+> pp t
  pp (EAddL e k t) = pp e <+> ":" <+> pp k <+> "+" <+> pp t
  pp (EAddR i e) = show i <+> "+" <+> pp e
  pp (ECase e (a,b) (c,d)) =
    smconcat ["case",pp e,"of",pp a,"->",pp b,"|",pp c,"->",pp d]
  pp (EAppFun e t) = pp e <+> pp t
  pp (EAppDest h e) = pp h <+> pp e
  pp (EAppArg v e) = undefined

data EnvCBN = EnvCBN { envCBN :: [(Variable,(FlatTerm,EnvCBN))] }
  deriving (Eq,Show)

instance Pretty EnvCBN where
  pp = braces
     . stringmconcat ", "
     . fmap (\(v,(t,e)) -> pp v <+> ":=" <+> pp t <+> "in" <+> pp e)
     . envCBN

instance (Pretty a, Pretty b, Pretty c) => Pretty (a,b,c) where
  pp (a,b,c) = stringmconcat " || " [pp b,pp c,pp a] <> "\n"

extendEnvCBN :: Variable -> (FlatTerm,EnvCBN) -> EnvCBN -> EnvCBN
extendEnvCBN v clos (EnvCBN e) = EnvCBN ((v,clos):e)

extendManyEnvCBN :: [(Variable,(FlatTerm,EnvCBN))] -> EnvCBN -> EnvCBN
extendManyEnvCBN vs (EnvCBN e) = EnvCBN (vs++e)

type EnvCBV = [(Variable,Val CallByValue)]

type MState s = (EnvCBN,EvalCtx s,FlatTerm)

interpPgm :: Program Term -> Std FlatTerm
interpPgm t =
  case runMachine (EnvCBN [],EEmpty,pgmTerm . flattenPgm $ t) of
    s@(_,_,t') -> trace (pp s) (return t')

runMachine :: s ~ CallByName => MState CallByName -> MState CallByName
runMachine = until finalState (\s -> trace (pp s) (step s))

finalState :: MState a -> Bool
finalState (_,EEmpty,FLit _) = True
finalState (_,EEmpty,FConsApp _ _) = True
finalState _ = False

step :: (s ~ CallByName) => MState s -> MState s
step (e,k,FLet v t1 t2) = ((extendEnvCBN v (t1,e) e), k, t2)
step s@(e,k,FVar v) =
  case lookup v (envCBN e) of
    Just (t,e') -> (e',k,t)
    Nothing -> error $ "unknown variable" <+> show v
step (e,k,FFix v t) = ((extendEnvCBN v (FFix v t,e) e), k, t)

step (e,k,FAdd t1 t2) = (e,EAddL e k t2,t1)
step (_,EAddL e' k r,FLit i) = (e',EAddR i k,r)
step (e,EAddR i k,FLit j) = (e,k,FLit (i+j))

step (e,k,FCase t a b) = (e,ECase k a b,t)
step (e,ECase k (p,u) (x,d),t@(FConsApp cons as)) =
  case p of
    FlatPatVar v  -> (extendEnvCBN v (t,e) e,k, u)
    FlatPatCons cons' ys ->
      case cons == cons' && length as == length ys of
        True  ->
          let e' = extendManyEnvCBN (zipWith (\a y -> (y,(a,e))) as ys) e
          in trace "match" (e',k,u)
        False -> trace "default" (extendEnvCBN x (t,e) e,k, d)

step (e,k,FCocase (FlatObsFun arg) t) = (e,EAppFun k arg,t)
step (e,k,FCocase (FlatObsDest h) t) = (e,EAppDest h k,t)

step (e,EAppFun k arg,FFun v t) = (extendEnvCBN v (arg,e) e,k,t)

step (e,EAppDest h k,FCoalt (h',u) d) =
  case h == h' of
    True  -> (e,k,u)
    False -> (e,k,d)

step (e,k,FEmpty) = error "unmatched (co)case"
step s = error $ "stuck on" <+> show s

-- reifyEvalCtx :: EvalCtx -> Term
-- reifyEvalCtx EEmpty      = undefined
-- reifyEvalCtx (EPrompt e) = Prompt (reifyEvalCtx e)
-- reifyEvalCtx (EAddL e t) = lam (Variable "t0") (Add (Var (Variable "t0")) t)
-- reifyEvalCtx (EAddR v e) = lam (Variable "t0")
--                                (Add (reifyValue v) (Var (Variable "t0")))
-- reifyEvalCtx (EAppFun e t) = lam (Variable "t0") (App (Var (Variable "t0")) t)
-- reifyEvalCtx (EAppDest v e) = lam (Variable "t0") (App (reifyValue v) undefined)

-- data Env = Env [(Variable,(Term,Env))]

-- lookupEnv :: Variable -> Env -> Std (Term,Env)
-- lookupEnv v (Env e) = lookupStd v e

-- instance Monoid Env where
--   mempty = Env []
--   mappend (Env a) (Env b) = Env (a <> b)

-- interpPgm :: Program Term -> Std Value
-- interpPgm = interpEmpty . pgmTerm

-- interpEmpty :: Term -> Std Value
-- interpEmpty = interp EEmpty mempty

-- interp :: EvalCtx -> Env -> Term -> Std Value
-- interp ctx env term =
--   case term of
--     Let x a b -> interp ctx (Env [(x,(a,env))] <> env) b
--     Prompt a -> interp (EPrompt ctx) env a
--     Lit i -> return (VLit i)
--     Add a b ->
--       do { a' <- interp (ctx `EAddL` b) env a
--          ; b' <- interp (a' `EAddR` ctx) env b
--          ; case (a',b') of
--              (VLit a'',VLit b'') -> return (VLit (a'' + b''))
--              _ -> typeErr "adding non-numbers"
--          }
--     Var v ->
--       do { (term',env') <- lookupEnv v env
--          ; interp ctx env' term' }
--     Fix x term' -> interp ctx (Env [(x,(term',env))] <> env) term'
--     App a b -> unimplementedErr "app"
--       -- do { a' <- interp (ctx `EAppL` b) env a
--       --    ; interp (a' `EAppR` ctx) env b }
--     Cons k -> return (VConsApp k [])
--     Case _ _ -> unimplementedErr "case"
--     Dest h -> return (VObs h)
--     Cocase _ _ -> unimplementedErr "cocase"
--     Coalts coalts -> comatch ctx env coalts

-- {- The outer comatch helper just goes through coalternatives by induction on the
-- list. -}
-- comatch :: EvalCtx -> Env -> [(CoPattern,Term)] -> Std Value
-- comatch ctx env ((cop,u):cas) =
--   comatch' ctx env cop >>= \m ->
--   case m of
--     Nothing -> comatch ctx env cas
--     Just (ctx',env') -> interp ctx' env' u
-- comatch _ _ [] = return VFail

-- {- Try to match with the outer most eval ctx at first, if that fails the try an
--    inner eval ctx.
-- -}
-- comatch' :: EvalCtx -> Env -> CoPattern -> Std (Maybe (EvalCtx,Env))
-- -- comatch' ctx env QHead = return (Just (ctx,env))

-- -- {- Covariables -}
-- -- comatch' ctx env (QVar a QHead) =
-- --   return (Just (EEmpty, Env [(a,(reifyEvalCtx ctx,env))] <> env))
-- -- comatch' ctx env (QVar a q) = comatch' ctx env q

-- -- {- Application forms -}
-- -- comatch' (EAppFun (VObs h) ctx) env (QDest h' q) =
-- --   case h == h' of
-- --      True -> comatch' ctx env q
-- --      False ->
-- --        do { m <- comatch' ctx env (QDest h' q)
-- --           ; case m of
-- --               Nothing -> return Nothing
-- --               Just (ctx', env') -> return $ Just (EAppDest (VObs h) ctx',env') }

-- comatch' _ _ _ = unimplementedErr "comatch'"
