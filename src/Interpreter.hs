{-# LANGUAGE GADTs, KindSignatures #-}
module Interpreter where

import Data.Monoid
import Utils
import VariableSyn
import DualSyn

data Value :: * where
  VLit     :: Int -> Value
  VConsApp :: Variable -> [Term] -> Value
  VObs     :: Variable -> Value
  VCocase  :: [(CoPattern,Term)] -> Value
  VFail    :: Value
  deriving Show

instance Pretty Value where
  pp (VLit i)        = show i
  pp (VConsApp k ts) = k <+> concatMap pp ts
  pp (VObs h)        = h
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
reifyEvalCtx (EAddL e t) = lam "t0" (Add (Var "t0") t)
reifyEvalCtx (EAddR v e) = lam "t0" (Add (reifyValue v) (Var "t0"))
reifyEvalCtx (EAppL e t) = lam "t0" (App (Var "t0") t)
reifyEvalCtx (EAppR v e) = lam "t0" (App (reifyValue v) undefined)

data Env = Env [(Variable,(Term,Env))]

lookupEnv :: Variable -> Env -> (Term,Env)
lookupEnv v (Env e) =
  case lookup v e of
    Nothing -> error "unbound variable"
    Just x -> x

instance Monoid Env where
  mempty = Env []
  mappend (Env a) (Env b) = Env (a <> b)

interpEmpty :: Term -> Value
interpEmpty = interp EEmpty mempty

interp :: EvalCtx -> Env -> Term -> Value
interp ctx env term =
  case term of
    Let x a b -> interp ctx (Env [(x,(a,env))] <> env) b
    Prompt a -> interp (EPrompt ctx) env a
    Lit i -> VLit i
    Add a b ->
      let a' = interp (ctx `EAddL` b) env a
          b' = interp (a' `EAddR` ctx) env b
      in
        case (a',b') of
          (VLit a'',VLit b'') -> VLit (a'' + b'')
          _ -> error "type error"
    Var v ->
      let (term',env') = lookupEnv v env
      in
        interp ctx env' term'
    Fix x term' -> interp ctx (Env [(x,(term',env))] <> env) term'
    App a b ->
      let a' = interp (ctx `EAppL` b) env a
      in
        interp (a' `EAppR` ctx) env b
    Cons k -> VConsApp k []
    Case _ _ -> undefined
    Dest h -> VObs h
    CoCase coalts -> comatch ctx env coalts

{- The outer comatch helper just goes through coalternatives by induction on the
list. -}
comatch :: EvalCtx -> Env -> [(CoPattern,Term)] -> Value
comatch ctx env ((cop,u):cas) =
  case comatch' ctx env cop of
    Nothing -> comatch ctx env cas
    Just (ctx',env') -> interp ctx' env' u
comatch _ _ [] = VFail

{- Try to match with the outer most eval ctx at first, if that fails the try an
   inner eval ctx.
-}
comatch' :: EvalCtx -> Env -> CoPattern -> Maybe (EvalCtx,Env)
comatch' ctx env QHead = Just (ctx,env)

{- Covariables -}
comatch' ctx env (QVar a QHead) =
  Just (EEmpty, Env [(a,(reifyEvalCtx ctx,env))] <> env)
comatch' ctx env (QVar a q) = comatch' ctx env q

{- Application forms -}
comatch' (EAppR (VObs h) ctx) env (QDest h' q) =
  case h == h' of
     True -> comatch' ctx env q
     False ->
       do { (ctx', env') <- comatch' ctx env (QDest h' q)
          ; return (EAppR (VObs h) ctx',env') }

comatch' _ _ _ = error "TODO{Comatch}"
