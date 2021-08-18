{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies #-}
module DL.Flat.Interpreter (interpPgm) where

import Control.Monad (when)
import Control.Arrow (second)
import DL.Utils.StdMonad
import DL.Utils.Pretty
import DL.Flat.Syntax
import DL.General.Top
import DL.General.Variable
import DL.General.Strategy

--------------------------------------------------------------------------------
--                            Olde Interpreter                                --
--------------------------------------------------------------------------------

data Result :: * where
  RNum     :: Int -> Result
  RConsApp :: Variable -> [Result] -> Result

resToFlatTerm :: Result -> FlatTerm
resToFlatTerm (RNum i) = FLit i
resToFlatTerm (RConsApp cons rs) = FConsApp cons (fmap resToFlatTerm rs)

instance Pretty Result where
  pp (RNum i) = show i
  pp (RConsApp cons rs) = pp cons <+> stringmconcat " " (fmap pp rs)

maybeCBVValue :: Env 'CallByValue -> FlatTerm -> Maybe (Value 'CallByValue)
maybeCBVValue _ (FLit i) = Just (VRes (RNum i))
maybeCBVValue e (FFun x t) = Just (VFunClos e x t)
maybeCBVValue e (FCoalt (h,t) def) = Just (VCoalt e (h,t) def)
maybeCBVValue e (FStreamCoiter b0 b1 t) =
  maybeCBVValue e t >>= \val -> Just (VCoiter e b0 b1 val)
maybeCBVValue _ _ = Nothing

data Value :: Strategy -> * where
  VFix :: FlatTerm -> Value strat

  VThunk :: Env 'CallByName -> FlatTerm -> Value 'CallByName

  VRes     :: Result -> Value 'CallByValue
  VFunClos :: Env 'CallByValue -> Variable -> FlatTerm -> Value 'CallByValue
  VCoalt   :: Env 'CallByValue -> (Variable,FlatTerm) -> FlatTerm
           -> Value 'CallByValue
  VCoiter  :: Env 'CallByValue -> (Variable,FlatTerm) -> (Variable,FlatTerm)
           -> Value 'CallByValue -> Value 'CallByValue

data Covalue (s :: Strategy) :: * where

data Env strat
  = Env { vars   :: [(Variable,Value strat)]
        , covars :: [(Variable,Covalue strat)]
        }

instance Pretty (Env strat) where
  pp = braces
     . stringmconcat ", "
     . fmap (\(v,_) -> pp v <+> ":= ...")
     . vars

extendEnvVar :: Variable -> Value strat -> Env strat -> Env strat
extendEnvVar x val (Env e c) = Env ((x,val):e) c

extendEnvCovar :: Variable -> Covalue strat -> Env strat -> Env strat
extendEnvCovar a coval (Env e c) = Env e ((a,coval):c)

extendManyEnvVar :: [(Variable,Value strat)] -> Env strat -> Env strat
extendManyEnvVar vs (Env e c) = Env (vs++e) c

emptyEnv :: Env strat
emptyEnv = Env [] []

data Cont (strat :: Strategy) :: * where
  CEmpty :: Cont strat
  CAddL :: Env strat -> FlatTerm -> Cont strat -> Cont strat
  CAddR :: Int -> Cont strat -> Cont strat
  CCase :: (FlatPattern,FlatTerm) -> (Variable,FlatTerm) -> Cont strat
        -> Cont strat
  CAppL :: Env strat -> FlatTerm -> Cont strat -> Cont strat
  CAppR :: Env 'CallByValue -> Variable -> FlatTerm -> Cont 'CallByValue
        -> Cont 'CallByValue
  CDest :: Variable  -> Cont strat -> Cont strat
  CCoiterR :: Env 'CallByValue -> (Variable,FlatTerm) -> (Variable,FlatTerm)
           -> Cont 'CallByValue -> Cont 'CallByValue
  CLetR :: Env 'CallByValue -> Variable -> FlatTerm -> Cont 'CallByValue
        -> Cont 'CallByValue
  -- EPrompt  :: EvalCtx s -> EvalCtx s
  -- -- call-by-value contexts
  -- ELet :: Variable FlatTerm

instance Pretty (Cont strat) where
  pp CEmpty = "#"
  pp (CAddL e t c) = "AddL" <+> pp e <+> pp t <+> "•" <+> pp c
  pp (CAddR i c) = "AddR" <+> show i <+> "•" <+> pp c
  pp (CAppL e t c) = "CAppL" <+> pp e <+> pp t <+> "•" <+> pp c
  pp (CAppR e x t c) = "CAppR" <+> pp e <+> pp x <+> pp t <+> "•" <+> pp c
  pp (CDest h c) = "CDest" <+> pp h <+> "•" <+> pp c
  pp (CCoiterR _ _ _ c) = "CCoiterR" <+> "•" <+> pp c
  pp (CLetR _ _ _ c) = "CLetR" <+> "•" <+> pp c

data MState strat
  = MState
  { env  :: Env strat
  , cont :: Cont strat
  , term :: FlatTerm }

instance Pretty (MState strat) where
  pp st = stringmconcat " ▮ " [pp (env st),pp (cont st),pp (term st)] <> "\n"

interpPgm :: Strategy -> Bool -> Program FlatTerm -> Std (Int,FlatTerm)
interpPgm s debug t =
  case s of
    CallByName -> second term <$> runMachine SingCBN debug 0 (MState emptyEnv CEmpty (pgmTerm $ t))
    CallByValue -> second term <$> runMachine SingCBV debug 0 (MState emptyEnv CEmpty (pgmTerm $ t))

runMachine :: StratSingleton strat
           -> Bool
           -> Int
           -> MState strat
           -> Std (Int, MState strat)
runMachine strat debug i st =
  do { when debug (logStd (pp st))
     ; case finalState st of
         True  -> return (i,st)
         False -> step strat st >>= runMachine strat debug (i+1) }

finalState :: MState a -> Bool
finalState (MState _ CEmpty (FLit _)) = True
finalState (MState _ CEmpty (FConsApp _ _)) = True
-- finalState (MState e (EPrompt k) t) = finalState (MState e k t)
finalState _ = False

step :: StratSingleton strat -> MState strat -> Std (MState strat)
step _ (MState e c (FPrompt t)) = return (MState e c t)

-- Variables; entering them
step SingCBV (MState e c (FVar x)) =
  case lookup x (vars e) of
    Just (VRes r) -> return (MState e c (resToFlatTerm r))
    Just (VFunClos e' y t) -> return (MState e' c (FFun y t))
    Just (VCoiter e' b0 b1 v) -> error "TODO{How does one enter a call-by-value coiterator}"
      -- return (MState e' c (FStreamCoiter b0 b1 s))
    Just (VCoalt e' m def) -> return (MState e' c (FCoalt m def))
    Just (VFix t) -> return (MState e c t)
    Nothing -> failure ("<unbound variable>:" <+> pp x)
step SingCBN (MState e c (FVar x)) =
  case lookup x (vars e) of
    Just (VThunk e' t) -> return (MState e' c t)
    Just (VFix t) -> return (MState e c t)
    Nothing -> failure ("<unbound variable>:" <+> pp x)

-- Fix
step _ (MState e c (FFix x t)) =
  return (MState (extendEnvVar x (VFix t) e) c t)

-- Addition
step _ (MState e c (FAdd t0 t1)) = return (MState e (CAddL e t1 c) t0)
step _ (MState _ (CAddL e t c) (FLit i)) = return (MState e (CAddR i c) t)
step _ (MState e (CAddR i c) (FLit j)) = return (MState e c (FLit (i+j)))

-- Applications
step _ (MState e c (FObsApp t0 t1)) = return (MState e (CAppL e t0 c) t1)
step SingCBN (MState e (CAppL e1 t1 c) (FFun x t)) =
  return (MState (extendEnvVar x (VThunk e1 t1) e) c t)
step SingCBV (MState e (CAppL e1 t1 c) (FFun x t)) =
  return (MState e1 (CAppR e x t c) t1)
step SingCBV (MState e1 (CAppR e x t c) t1)
  | Just val <- maybeCBVValue e1 t1
  = return (MState (extendEnvVar x val e) c t)

-- General codata obs
step _ (MState e c (FObsDest h t))
  = return (MState e (CDest h c) t)

step _ (MState e (CDest h c) (FCoalt (h',t0) t1))
 = case h == h' of
     True -> return (MState e c t0)
     False -> return (MState e (CDest h c) t1)

-- Coiter codata
step SingCBN (MState e (CDest h c) (FStreamCoiter (x,t0) (y,t1) t2))
  = case h of
      -- NOTA BENE: Here I just check that the first part of the destructor is
      -- 'Head' or 'Tail' since the renamer will create new names for these that
      -- have numbers at the end. This will break if a user defines a codata
      -- type with a destructor that begins with 'Head' or 'Tail', but is not
      -- the canonical stream one.
      Variable ('H':'e':'a':'d':_) ->
        return (MState (extendEnvVar x (VThunk e t2) e) c t0)
      Variable ('T':'a':'i':'l':_) ->
        return (MState (extendEnvVar y (VThunk e t2) e)
                       c
                       (FStreamCoiter (x,t0) (y,t1) t1))
      _  -> failure $ "<observation error>: cannot observe" <+> pp h
step SingCBV (MState e (CDest h c) (FStreamCoiter (x,t0) (y,t1) t2))
  | Nothing <- maybeCBVValue e t2
  = return (MState e (CDest h c) (FStreamCoiter (x,t0) (y,t1) t2))
step SingCBV (MState e (CCoiterR e' (x,t0) (y,t1) (CDest h c)) t2)
  | Just val <- maybeCBVValue e t2
  = case h of
      -- NOTA BENE: Here I just check that the first part of the destructor is
      -- 'Head' or 'Tail' since the renamer will create new names for these that
      -- have numbers at the end. This will break if a user defines a codata
      -- type with a destructor that begins with 'Head' or 'Tail', but is not
      -- the canonical stream one.
      Variable ('H':'e':'a':'d':_) ->
        return (MState (extendEnvVar x val e') c t0)
      Variable ('T':'a':'i':'l':_) ->
        return (MState (extendEnvVar y val e')
                       c
                       (FStreamCoiter (x,t0) (y,t1) t1))
      _  -> failure $ "<observation error>: cannot observe" <+> pp h

-- Let expressions
step SingCBN (MState e c (FLet x t0 t1))
  = return (MState (extendEnvVar x (VThunk e t0) e) c t1)
step SingCBV (MState e c (FLet x t0 t1))
  = return (MState e (CLetR e x t1 c) t0)
step SingCBV (MState e (CLetR e' x t1 c) t0)
  | Just val <- maybeCBVValue e t0
  = return (MState (extendEnvVar x val e') c t1)

-- A stuck program
step _ _ = failure "<stuck>"

  --   return (MState (extendEnvVar v (t1,e) e) k t2)
-- step (MState e k (FVar v)) =
--   case lookup v (vars e) of
--     Just (t,e') -> return (MState e' k t)
--     Nothing    ->
--       do { states <- get
--          ; let string = vmconcat . fmap pp $ states
--          ; lift (failure $ string <-> "<unbound>" <+> show v) }

-- step (MState e k (FFix v t)) =
--   return (MState (extendEnvVar v (FFix v t,e) e) k t)

-- step (MState e k (FAdd t1 t2)) = return (MState e (EAddL e k t2) t1)
-- step (MState _ (EAddL e' k r) (FLit i)) = return (MState e' (EAddR i k) r)
-- step (MState e (EAddR i k) (FLit j)) = return (MState e k (FLit (i+j)))

-- step (MState e k (FCase t a b)) = return (MState e (ECase k a b) t)
-- step (MState e (ECase k (p,u) (x,d)) t@(FConsApp cons as)) =
--   case p of
--     FlatPatVar v  -> return (MState (extendEnvVar v (t,e) e) k u)
--     FlatPatCons cons' ys ->
--       case cons == cons' && length as == length ys of
--         True  ->
--           let e' = extendManyEnvVar (zipWith (\a y -> (y,(a,e))) as ys) e
--           in return (MState e' k u)
--         False -> return (MState (extendEnvVar x (t,e) e) k d)

-- step (MState e k (FObsApp arg t)) =
--   return (MState e (EAppFun k arg) t)
-- step (MState e k (FObsDest h t)) =
--   return (MState e (EAppDest h k) t)
-- step (MState e k (FObsCut v t)) =
--   case lookup v (covars e) of
--     Just k' -> return (MState e (plugEvalCtx k k') t)
--     Nothing ->
--       do { states <- get
--          ; let string = vmconcat . fmap pp $ states
--          ; lift (failure $ string <-> "<unbound covariable>" <+> show v) }

-- step (MState e (EAppFun k arg) (FFun v t)) =
--   return (MState (extendEnvVar v (arg,e) e) k t)

-- step (MState e (EAppDest h k) (FCoalt (h',u) d)) =
--   case h == h' of
--     True  -> return (MState e k u)
--     False -> return (MState e k d)

-- step (MState _ _ FEmpty) =
--   do { states <- get
--      ; let string = vmconcat . fmap pp $ states
--      ; lift (failure $ string <-> "<unmatched (co)case>") }

-- -- ^ We split the context up to the first prompt
-- step (MState e k (FShift v t)) =
--   let (k',mk) = splitEvalCtx k in
--     case mk of
--       Nothing -> return (MState (extendEnvCovar v k' e) EEmpty t)
--       Just k'' -> return (MState (extendEnvCovar v k' e) k'' t)

-- step (MState e k (FPrompt t)) =
--   return (MState e (EPrompt k) t)

-- step (MState e (EAppDest h k) (FStreamCoiter (x,a) (y,b) c))
--   | h == Variable "Head" = return (MState (extendEnvVar x c e) k a)


-- -- | subsititute a context for the hole
-- plugEvalCtx :: (s ~ 'CallByName) => EvalCtx s -> EvalCtx s -> EvalCtx s
-- plugEvalCtx EEmpty k' = k'
-- plugEvalCtx (EAddL e k t) k' = EAddL e (plugEvalCtx k k') t
-- plugEvalCtx (EAddR i k) k' = EAddR i (plugEvalCtx k k')
-- plugEvalCtx (ECase k alt def) k' = ECase (plugEvalCtx k k') alt def
-- plugEvalCtx (EAppFun k t) k' = EAppFun (plugEvalCtx k k') t
-- plugEvalCtx (EAppDest h k) k' = EAppDest h (plugEvalCtx k k')
-- plugEvalCtx (EPrompt k) k' = EPrompt (plugEvalCtx k k')

-- splitEvalCtx :: (s ~ 'CallByName) => EvalCtx s -> (EvalCtx s, Maybe (EvalCtx s))
-- splitEvalCtx EEmpty = (EEmpty, Nothing)
-- splitEvalCtx (EAddL e k t) = let (k',mk) = splitEvalCtx k in (EAddL e k' t,mk)
-- splitEvalCtx (EAddR i k) = let (k',mk) = splitEvalCtx k in (EAddR i k',mk)
-- splitEvalCtx (ECase k alt def) =
--   let (k',mk) = splitEvalCtx k in
--     (ECase k' alt def,mk)
-- splitEvalCtx (EAppFun k t) =
--   let (k',mk) = splitEvalCtx k in
--     (EAppFun k' t, mk)
-- splitEvalCtx (EAppDest h k) =
--   let (k',mk) = splitEvalCtx k in
--     (EAppDest h k', mk)
-- splitEvalCtx (EPrompt k) =
--   let (k',mk) = splitEvalCtx k in
--     case mk of
--       Nothing -> (EEmpty,Just k')
--       _ -> (k',mk)

-- instance Eq (EvalCtx s) where
--   EEmpty == EEmpty = True
--   (EAddL e a t)  == (EAddL e' b u) = e == e' && a == b && t == u
--   (EAddR v a)    == (EAddR w b)    = a == b && v == w
--   (ECase e a b)  == (ECase f c d)  = e == f && a == c && b == d
--   (EAppFun a t)  == (EAppFun b e)  = a == b && t == e
--   (EAppDest v a) == (EAppDest w b) = a == b && v == w
--   (EPrompt a)    == (EPrompt b)    = a == b
--   _ == _ = False

-- instance Show (EvalCtx s) where
--   show EEmpty = "#"
--   show (EAddL e k t) = show e <+> show k <+> "+" <+> show t
--   show (EAddR i e) = show i <+> "+" <+> show e
--   show (ECase e a b) = "case" <+> show e <+> show a <+> "|" <+> show b
--   show (EAppFun e t) = show e <+> show t
--   show (EAppDest h e) = show h <+> show e
--   show (EPrompt e) = "#" <+> show e

-- instance Pretty (EvalCtx s) where
--   pp EEmpty = "#"
--   pp (EAddL e k t) = pp e <+> ":" <+> pp k <+> "+" <+> pp t
--   pp (EAddR i e) = show i <+> "+" <+> pp e
--   pp (ECase e (a,b) (c,d)) =
--     smconcat ["case",pp e,"{",pp a,"->",pp b,"|",pp c,"->",pp d,"}"]
--   pp (EAppFun e t) = pp e <+> pp t
--   pp (EAppDest h e) = pp h <+> pp e
--   pp (EPrompt k) = "#" <+> pp k
