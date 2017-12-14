{-# LANGUAGE GADTs, KindSignatures, UnicodeSyntax #-}
module Interpreter where

import Data.Monoid

import Utils
import VariableSyn
import DualSyn
import Pretty

data Value :: * where
  VLit     :: Int -> Value
  VConsApp :: Variable -> [Term] -> Value
  VObs     :: Variable -> Value
  VCocase  :: [(CoPattern,Term)] -> Value
  VFail    :: Value
  deriving Show

instance Pretty Value where
  pp (VLit i)        = show i
  pp (VConsApp k ts) = pp k <+> concatMap pp ts
  pp (VObs h)        = pp h
  pp (VCocase cas)   = pp (CoCase cas)
  pp VFail           = "⊥"

reifyValue :: Value -> Term
reifyValue (VLit i) = Lit i
reifyValue (VConsApp k ts) = distributeArgs (k,ts)
reifyValue (VObs h) = Dest h
reifyValue (VCocase cas) = CoCase cas
reifyValue VFail = CoCase []

data EvalCtx :: * where
  EEmpty  :: EvalCtx
  EPrompt :: EvalCtx -> EvalCtx
  EAddL   :: EvalCtx -> Term    -> EvalCtx
  EAddR   :: Value   -> EvalCtx -> EvalCtx
  EAppL   :: EvalCtx -> Term    -> EvalCtx
  EAppR   :: Value   -> EvalCtx -> EvalCtx

reifyEvalCtx :: EvalCtx -> Term
reifyEvalCtx EEmpty      = undefined
reifyEvalCtx (EPrompt e) = Prompt (reifyEvalCtx e)
reifyEvalCtx (EAddL e t) = lam (Variable "t0") (Add (Var (Variable "t0")) t)
reifyEvalCtx (EAddR v e) = lam (Variable "t0")
                               (Add (reifyValue v) (Var (Variable "t0")))
reifyEvalCtx (EAppL e t) = lam (Variable "t0") (App (Var (Variable "t0")) t)
reifyEvalCtx (EAppR v e) = lam (Variable "t0") (App (reifyValue v) undefined)

data Env = Env [(Variable,(Term,Env))]

lookupEnv :: Variable -> Env -> Std (Term,Env)
lookupEnv v (Env e) = lookupStd v e

instance Monoid Env where
  mempty = Env []
  mappend (Env a) (Env b) = Env (a <> b)

interpPgm :: Program Term → Std Value
interpPgm = interpEmpty . pgmTerm

interpEmpty :: Term -> Std Value
interpEmpty = interp EEmpty mempty

interp :: EvalCtx -> Env -> Term -> Std Value
interp ctx env term =
  case term of
    Let x a b -> interp ctx (Env [(x,(a,env))] <> env) b
    Prompt a -> interp (EPrompt ctx) env a
    Lit i -> return (VLit i)
    Add a b ->
      do { a' <- interp (ctx `EAddL` b) env a
         ; b' <- interp (a' `EAddR` ctx) env b
         ; case (a',b') of
             (VLit a'',VLit b'') -> return (VLit (a'' + b''))
             _ -> typeErr "adding non-numbers"
         }
    Var v ->
      do { (term',env') <- lookupEnv v env
         ; interp ctx env' term' }
    Fix x term' -> interp ctx (Env [(x,(term',env))] <> env) term'
    App a b ->
      do { a' <- interp (ctx `EAppL` b) env a
         ; interp (a' `EAppR` ctx) env b }
    Cons k -> return (VConsApp k [])
    Case _ _ -> unimplementedErr "case"
    Dest h -> return (VObs h)
    CoCase coalts -> comatch ctx env coalts

{- The outer comatch helper just goes through coalternatives by induction on the
list. -}
comatch :: EvalCtx -> Env -> [(CoPattern,Term)] -> Std Value
comatch ctx env ((cop,u):cas) =
  comatch' ctx env cop >>= \m ->
  case m of
    Nothing -> comatch ctx env cas
    Just (ctx',env') -> interp ctx' env' u
comatch _ _ [] = return VFail

{- Try to match with the outer most eval ctx at first, if that fails the try an
   inner eval ctx.
-}
comatch' :: EvalCtx -> Env -> CoPattern -> Std (Maybe (EvalCtx,Env))
comatch' ctx env QHead = return (Just (ctx,env))

{- Covariables -}
comatch' ctx env (QVar a QHead) =
  return (Just (EEmpty, Env [(a,(reifyEvalCtx ctx,env))] <> env))
comatch' ctx env (QVar a q) = comatch' ctx env q

{- Application forms -}
comatch' (EAppR (VObs h) ctx) env (QDest h' q) =
  case h == h' of
     True -> comatch' ctx env q
     False ->
       do { m <- comatch' ctx env (QDest h' q)
          ; case m of
              Nothing -> return Nothing
              Just (ctx', env') -> return $ Just (EAppR (VObs h) ctx',env') }

comatch' _ _ _ = unimplementedErr "comatch'"
