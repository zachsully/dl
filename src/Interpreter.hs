{-# LANGUAGE GADTs, KindSignatures #-}
module Interpreter where

import Data.Monoid

import VariableSyn
import DualSyn

data Value :: * where
  VLit     :: Int -> Value
  VConsApp :: Variable -> [Term] -> Value
  VObs     :: Variable -> Value
  VCocase  :: [(CoPattern,Term)] -> Value
  VFail    :: Value
  deriving Show

data EvalCtx :: * where
  EEmpty :: EvalCtx
  EAddL  :: EvalCtx -> Term  -> EvalCtx
  EAddR  :: EvalCtx -> Value -> EvalCtx
  EAppL  :: EvalCtx -> Term  -> EvalCtx
  EAppR  :: EvalCtx -> Value -> EvalCtx

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
    Lit i -> VLit i
    Add a b ->
      let a' = interp (ctx `EAddL` b) env a
          b' = interp (ctx `EAddR` a') env b
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
        interp (ctx `EAppR` a') env b
    Cons k -> VConsApp k []
    Case _ _ -> undefined
    Dest h -> VObs h
    CoCase coalts -> comatch ctx env coalts

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

comatch' (EAppR ctx (VObs h)) env (QDest h' q) =
  case h == h' of
     True -> comatch' ctx env q
     False ->
       do { (ctx', env') <- comatch' ctx env (QDest h' q)
          ; return (EAppR ctx' (VObs h),env') }

comatch' _ _ _ = undefined
