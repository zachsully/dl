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
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Evaluation.Strategy

data EvalCtx :: Strategy -> * where
  EEmpty   :: EvalCtx s
  EAddL    :: EnvCBN    -> EvalCtx s -> FlatTerm  -> EvalCtx s
  EAddR    :: Int       -> EvalCtx s -> EvalCtx s
  ECase    :: EvalCtx s -> (FlatPattern,FlatTerm) -> (Variable,FlatTerm)
           -> EvalCtx s
  EAppFun  :: EvalCtx s -> FlatTerm -> EvalCtx s
  EAppDest :: Variable  -> EvalCtx s -> EvalCtx s
  EPrompt  :: EvalCtx s -> EvalCtx s

-- | subsititute a context for the hole
plugEvalCtx :: (s ~ 'CallByName) => EvalCtx s -> EvalCtx s -> EvalCtx s
plugEvalCtx EEmpty k' = k'
plugEvalCtx (EAddL e k t) k' = EAddL e (plugEvalCtx k k') t
plugEvalCtx (EAddR i k) k' = EAddR i (plugEvalCtx k k')
plugEvalCtx (ECase k alt def) k' = ECase (plugEvalCtx k k') alt def
plugEvalCtx (EAppFun k t) k' = EAppFun (plugEvalCtx k k') t
plugEvalCtx (EAppDest h k) k' = EAppDest h (plugEvalCtx k k')
plugEvalCtx (EPrompt k) k' = EPrompt (plugEvalCtx k k')

splitEvalCtx :: (s ~ 'CallByName) => EvalCtx s -> (EvalCtx s, Maybe (EvalCtx s))
splitEvalCtx EEmpty = (EEmpty, Nothing)
splitEvalCtx (EAddL e k t) = let (k',mk) = splitEvalCtx k in (EAddL e k' t,mk)
splitEvalCtx (EAddR i k) = let (k',mk) = splitEvalCtx k in (EAddR i k',mk)
splitEvalCtx (ECase k alt def) =
  let (k',mk) = splitEvalCtx k in
    (ECase k' alt def,mk)
splitEvalCtx (EAppFun k t) =
  let (k',mk) = splitEvalCtx k in
    (EAppFun k' t, mk)
splitEvalCtx (EAppDest h k) =
  let (k',mk) = splitEvalCtx k in
    (EAppDest h k', mk)
splitEvalCtx (EPrompt k) =
  let (k',mk) = splitEvalCtx k in
    case mk of
      Nothing -> (EEmpty,Just k')
      _ -> (k',mk)

instance Eq (EvalCtx s) where
  EEmpty == EEmpty = True
  (EAddL e a t)  == (EAddL e' b u) = e == e' && a == b && t == u
  (EAddR v a)    == (EAddR w b)    = a == b && v == w
  (ECase e a b)  == (ECase f c d)  = e == f && a == c && b == d
  (EAppFun a t)  == (EAppFun b e)  = a == b && t == e
  (EAppDest v a) == (EAppDest w b) = a == b && v == w
  (EPrompt a)    == (EPrompt b)    = a == b
  _ == _ = False

instance Show (EvalCtx s) where
  show EEmpty = "#"
  show (EAddL e k t) = show e <+> show k <+> "+" <+> show t
  show (EAddR i e) = show i <+> "+" <+> show e
  show (ECase e a b) = "case" <+> show e <+> show a <+> "|" <+> show b
  show (EAppFun e t) = show e <+> show t
  show (EAppDest h e) = show h <+> show e
  show (EPrompt e) = "#" <+> show e

instance Pretty (EvalCtx s) where
  pp EEmpty = "#"
  pp (EAddL e k t) = pp e <+> ":" <+> pp k <+> "+" <+> pp t
  pp (EAddR i e) = show i <+> "+" <+> pp e
  pp (ECase e (a,b) (c,d)) =
    smconcat ["case",pp e,"{",pp a,"->",pp b,"|",pp c,"->",pp d,"}"]
  pp (EAppFun e t) = pp e <+> pp t
  pp (EAppDest h e) = pp h <+> pp e
  pp (EPrompt k) = "#" <+> pp k

data EnvCBN
  = EnvCBN { vars   :: [(Variable,(FlatTerm,EnvCBN))]
           , covars :: [(Variable,EvalCtx 'CallByName)]}
  deriving (Eq,Show)

instance Pretty EnvCBN where
  pp = braces
     . stringmconcat ", "
     . fmap (\(v,(t,e)) -> pp v <+> ":=" <+> pp t <+> "in" <+> pp e)
     . vars

extendEnvVar :: Variable -> (FlatTerm,EnvCBN) -> EnvCBN -> EnvCBN
extendEnvVar v clos (EnvCBN e c) = EnvCBN ((v,clos):e) c

extendEnvCovar :: Variable -> EvalCtx 'CallByName -> EnvCBN -> EnvCBN
extendEnvCovar v ctx (EnvCBN e c) = EnvCBN e ((v,ctx):c)

extendManyEnvVar :: [(Variable,(FlatTerm,EnvCBN))] -> EnvCBN -> EnvCBN
extendManyEnvVar vs (EnvCBN e c) = EnvCBN (vs++e) c

emptyEnvCBN :: EnvCBN
emptyEnvCBN = EnvCBN [] []

data MState s = MState EnvCBN (EvalCtx s) FlatTerm

instance Pretty (MState s) where
  pp (MState a b c) = "⟨" <+> stringmconcat " !¡ " [pp b,pp c,pp a] <+> "⟩\n"

interpPgm :: Program FlatTerm -> Std FlatTerm
interpPgm t =
  let mrun   = runMachine (MState emptyEnvCBN EEmpty (pgmTerm $ t))
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
finalState (MState e (EPrompt k) t) = finalState (MState e k t)
finalState _ = False

step :: (s ~ 'CallByName) => MState s -> StateT [MState s] Std (MState s)
step (MState e k (FLet v t1 t2)) =
  return (MState (extendEnvVar v (t1,e) e) k t2)
step (MState e k (FVar v)) =
  case lookup v (vars e) of
    Just (t,e') -> return (MState e' k t)
    Nothing    ->
      do { states <- get
         ; let string = vmconcat . fmap pp $ states
         ; lift (failure $ string <-> "<unbound>" <+> show v) }

step (MState e k (FFix v t)) =
  return (MState (extendEnvVar v (FFix v t,e) e) k t)

step (MState e k (FAdd t1 t2)) = return (MState e (EAddL e k t2) t1)
step (MState _ (EAddL e' k r) (FLit i)) = return (MState e' (EAddR i k) r)
step (MState e (EAddR i k) (FLit j)) = return (MState e k (FLit (i+j)))

step (MState e k (FCase t a b)) = return (MState e (ECase k a b) t)
step (MState e (ECase k (p,u) (x,d)) t@(FConsApp cons as)) =
  case p of
    FlatPatVar v  -> return (MState (extendEnvVar v (t,e) e) k u)
    FlatPatCons cons' ys ->
      case cons == cons' && length as == length ys of
        True  ->
          let e' = extendManyEnvVar (zipWith (\a y -> (y,(a,e))) as ys) e
          in return (MState e' k u)
        False -> return (MState (extendEnvVar x (t,e) e) k d)

step (MState e k (FCocase (FlatObsFun arg) t)) =
  return (MState e (EAppFun k arg) t)
step (MState e k (FCocase (FlatObsDest h) t)) =
  return (MState e (EAppDest h k) t)
step (MState e k (FCocase (FlatObsCut v) t)) =
  case lookup v (covars e) of
    Just k' -> return (MState e (plugEvalCtx k k') t)
    Nothing ->
      do { states <- get
         ; let string = vmconcat . fmap pp $ states
         ; lift (failure $ string <-> "<unbound covariable>" <+> show v) }

step (MState e (EAppFun k arg) (FFun v t)) =
  return (MState (extendEnvVar v (arg,e) e) k t)

step (MState e (EAppDest h k) (FCoalt (h',u) d)) =
  case h == h' of
    True  -> return (MState e k u)
    False -> return (MState e k d)

step (MState _ _ FEmpty) =
  do { states <- get
     ; let string = vmconcat . fmap pp $ states
     ; lift (failure $ string <-> "<unmatched (co)case>") }

-- ^ We split the context up to the first prompt
step (MState e k (FShift v t)) =
  let (k',mk) = splitEvalCtx k in
    case mk of
      Nothing -> return (MState (extendEnvCovar v k' e) EEmpty t)
      Just k'' -> return (MState (extendEnvCovar v k'' e) k' t)

step (MState e k (FPrompt t)) =
  return (MState e (EPrompt k) t)

step s = do { states <- get
            ; let string = vmconcat . fmap pp $ states
            ; lift (failure $ string <-> "\n<stuck>:" <-> pp s) }
