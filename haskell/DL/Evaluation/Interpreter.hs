{-# LANGUAGE
      DataKinds,
      GADTs,
      KindSignatures,
      TypeFamilies,
      UnicodeSyntax
#-}
module DL.Evaluation.Interpreter ( interpPgm ) where

import Control.Monad.State
import DL.Utils
import DL.Pretty
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Evaluation.Strategy

-- data Val :: Strategy -> * where
--   VTerm     :: FlatTerm -> Val CallByName
--   VLit      :: Int -> Val s
--   VConsVal  :: Variable -> [Val CallByValue] -> Val CallByValue
--   VConsTerm :: Variable -> [FlatTerm] -> Val CallByName
--   VFun      :: Variable -> FlatTerm -> Val s
--   VCoalt    :: (Variable,FlatTerm) -> FlatTerm -> Val s
--   VEmpty    :: Val s

-- instance Eq (Val s) where
--   (VTerm a)       == (VTerm b)  = a == b
--   (VLit i)        == (VLit j)   = i == j
--   (VConsVal k vs) == (VConsVal j ws) = k == j && vs == ws

-- instance Show (Val s) where
--   show (VTerm t) = show t

-- instance Pretty (Val s) where
--   pp (VTerm t) = pp t

data EvalCtx :: Strategy -> * where
  EEmpty   :: EvalCtx s
  EPrompt  :: EvalCtx s -> EvalCtx s
  EAddL    :: EnvCBN    -> EvalCtx s -> FlatTerm  -> EvalCtx s
  EAddR    :: Int       -> EvalCtx s -> EvalCtx s
  ECase    :: EvalCtx s -> (FlatPattern,FlatTerm) -> (Variable,FlatTerm)
           -> EvalCtx s
  EAppFun  :: EvalCtx s -> FlatTerm -> EvalCtx s
  EAppDest :: Variable  -> EvalCtx s -> EvalCtx s
  -- EAppArg  :: (cbv ~ CallByValue) => Val cbv -> EvalCtx cbv -> EvalCtx cbv

instance Eq (EvalCtx s) where
  EEmpty == EEmpty = True
  (EPrompt a)    == (EPrompt b)    = a == b
  (EAddL e a t)  == (EAddL e' b u) = e == e' && a == b && t == u
  (EAddR v a)    == (EAddR w b)    = a == b && v == w
  (ECase e a b)  == (ECase f c d)  = e == f && a == c && b == d
  (EAppFun a t)  == (EAppFun b e)  = a == b && t == e
  (EAppDest v a) == (EAppDest w b) = a == b && v == w
  -- (EAppArg v a)  == (EAppArg w b)  = a == b && v == w
  _ == _ = False

instance Show (EvalCtx s) where
  show EEmpty = "#"
  show (EPrompt t) = "#" <+> show t
  show (EAddL e k t) = show e <+> show k <+> "+" <+> show t
  show (EAddR i e) = show i <+> "+" <+> show e
  show (ECase e a b) = "case" <+> show e <+> show a <+> "|" <+> show b
  show (EAppFun e t) = show e <+> show t
  show (EAppDest h e) = show h <+> show e
  -- show (EAppArg v e) = undefined

instance Pretty (EvalCtx s) where
  pp EEmpty = "#"
  pp (EPrompt t) = "#" <+> pp t
  pp (EAddL e k t) = pp e <+> ":" <+> pp k <+> "+" <+> pp t
  pp (EAddR i e) = show i <+> "+" <+> pp e
  pp (ECase e (a,b) (c,d)) =
    smconcat ["case",pp e,"{",pp a,"->",pp b,"|",pp c,"->",pp d,"}"]
  pp (EAppFun e t) = pp e <+> pp t
  pp (EAppDest h e) = pp h <+> pp e
  -- pp (EAppArg v e) = undefined

data EnvCBN = EnvCBN { envCBN :: [(Variable,(FlatTerm,EnvCBN))] }
  deriving (Eq,Show)

instance Pretty EnvCBN where
  pp = braces
     . stringmconcat ", "
     . fmap (\(v,(t,e)) -> pp v <+> ":=" <+> pp t <+> "in" <+> pp e)
     . envCBN

extendEnvCBN :: Variable -> (FlatTerm,EnvCBN) -> EnvCBN -> EnvCBN
extendEnvCBN v clos (EnvCBN e) = EnvCBN ((v,clos):e)

extendManyEnvCBN :: [(Variable,(FlatTerm,EnvCBN))] -> EnvCBN -> EnvCBN
extendManyEnvCBN vs (EnvCBN e) = EnvCBN (vs++e)

emptyEnvCBN :: EnvCBN
emptyEnvCBN = EnvCBN []

data MState s = MState EnvCBN (EvalCtx s) FlatTerm

instance Pretty (MState s) where
  pp (MState a b c) = "⟨" <+> stringmconcat " !¡ " [pp b,pp c,pp a] <+> "⟩\n"

interpPgm :: Program Term -> Std FlatTerm
interpPgm t =
  let mrun   = runMachine (MState emptyEnvCBN EEmpty (pgmTerm . flattenPgm $ t))
      ss = runStateT mrun [] in
    ss >>= (\(MState _ _ t',_) -> return t')

runMachine :: s ~ 'CallByName
           => MState s
           -> StateT [MState s] Std (MState s)
runMachine s =
  do { put . (s:) =<< get
     ; s' <- step s
     ; case finalState s' of
         True  -> return s'
         False -> runMachine s' }

finalState :: MState a -> Bool
finalState (MState _ EEmpty (FLit _)) = True
finalState (MState _ EEmpty (FConsApp _ _)) = True
finalState _ = False

step :: (s ~ 'CallByName) => MState s -> StateT [MState s] Std (MState s)
step (MState e k (FLet v t1 t2)) =
  return (MState (extendEnvCBN v (t1,e) e) k t2)
step (MState e k (FVar v)) =
  case lookup v (envCBN e) of
    Just (t,e') -> return (MState e' k t)
    Nothing    ->
      do { states <- get
         ; let string = vmconcat . fmap pp $ states
         ; lift (failure $ string <-> "<unbound>" <+> show v) }

step (MState e k (FFix v t)) =
  return (MState (extendEnvCBN v (FFix v t,e) e) k t)

step (MState e k (FAdd t1 t2)) = return (MState e (EAddL e k t2) t1)
step (MState _ (EAddL e' k r) (FLit i)) = return (MState e' (EAddR i k) r)
step (MState e (EAddR i k) (FLit j)) = return (MState e k (FLit (i+j)))

step (MState e k (FCase t a b)) = return (MState e (ECase k a b) t)
step (MState e (ECase k (p,u) (x,d)) t@(FConsApp cons as)) =
  case p of
    FlatPatVar v  -> return (MState (extendEnvCBN v (t,e) e) k u)
    FlatPatCons cons' ys ->
      case cons == cons' && length as == length ys of
        True  ->
          let e' = extendManyEnvCBN (zipWith (\a y -> (y,(a,e))) as ys) e
          in return (MState e' k u)
        False -> return (MState (extendEnvCBN x (t,e) e) k d)

step (MState e k (FCocase (FlatObsFun arg) t)) =
  return (MState e (EAppFun k arg) t)
step (MState e k (FCocase (FlatObsDest h) t)) =
  return (MState e (EAppDest h k) t)

step (MState e (EAppFun k arg) (FFun v t)) =
  return (MState (extendEnvCBN v (arg,e) e) k t)

step (MState e (EAppDest h k) (FCoalt (h',u) d)) =
  case h == h' of
    True  -> return (MState e k u)
    False -> return (MState e k d)

step (MState _ _ FEmpty) =
  do { states <- get
     ; let string = vmconcat . fmap pp $ states
     ; lift (failure $ string <-> "<unmatched (co)case>") }
step s = do { states <- get
            ; let string = vmconcat . fmap pp $ states
            ; lift (failure $ string <-> "\n<stuck>:" <-> pp s) }
