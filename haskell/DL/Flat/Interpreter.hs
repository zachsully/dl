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

maybeCBVValue :: Env 'CallByValue -> FlatTerm -> Maybe (Value 'CallByValue)
maybeCBVValue _ (FLit i) = Just (VLit i)
maybeCBVValue e (FFun x t) = Just (VFunClos e x t)
maybeCBVValue e (FCoalt (h,t) def) = Just (VCoalt e (h,t) def)
maybeCBVValue _ _ = Nothing

valToFlatTerm :: Value strat -> FlatTerm
valToFlatTerm (VLit i) = FLit i
valToFlatTerm (VConsApp cons vs) = FConsApp cons (fmap valToFlatTerm vs)
valToFlatTerm _ = error "valToFlatTerm"

data Value :: Strategy -> * where
  VFix :: FlatTerm -> Value strat

  VThunk :: Env 'CallByName -> FlatTerm -> Value 'CallByName

  VLit :: Int -> Value 'CallByValue
  VConsApp :: Variable -> [Value 'CallByValue] -> Value 'CallByValue
  VFunClos :: Env 'CallByValue -> Variable -> FlatTerm -> Value 'CallByValue
  VCoalt :: Env 'CallByValue -> (Variable,FlatTerm) -> FlatTerm
         -> Value 'CallByValue
  VCoiter :: Env 'CallByValue -> (Variable,FlatTerm) -> (Variable,FlatTerm)
          -> Value 'CallByValue -> Value 'CallByValue

instance Pretty (Value strat) where
  pp (VFix _) = "<fixpoint>"
  pp (VThunk e _) = "<thunk" <+> pp e <> ">"
  pp (VLit i) = show i
  pp (VConsApp cons vs) = pp cons <+> stringmconcat " " (fmap pp vs)
  pp (VFunClos e x t) = "<function" <+> pp e <+> pp x <+> ">"
  pp (VCoalt e x t) = "<codata" <+> pp e <+> ">"
  pp (VCoiter e _ _ s) = "<coiter" <+> pp e <+> pp s <+> ">"

data Covalue (s :: Strategy) :: * where

data Env strat
  = Env { vars   :: [(Variable,Value strat)]
        , covars :: [(Variable,Covalue strat)]
        }

instance Pretty (Env strat) where
  pp = braces
     . stringmconcat ", "
     . fmap (\(v,_) -> pp v)
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
  CPrompt :: Cont strat -> Cont strat
  CForce :: Cont strat -> Cont strat
  CRet :: Value 'CallByValue -> Cont 'CallByValue -> Cont 'CallByValue
  CAddL :: Env strat -> FlatTerm -> Cont strat -> Cont strat
  CAddR :: Int -> Cont strat -> Cont strat
  CCase :: Env strat -> (FlatPattern,FlatTerm) -> (Variable,FlatTerm) -> Cont strat
        -> Cont strat
  CArg :: Env strat -> FlatTerm -> Cont strat -> Cont strat
  CFun :: Env 'CallByValue -> Variable -> FlatTerm -> Cont 'CallByValue
        -> Cont 'CallByValue
  CDest :: Variable  -> Cont strat -> Cont strat
  CCoiterR :: Env 'CallByValue -> (Variable,FlatTerm) -> (Variable,FlatTerm)
           -> Cont 'CallByValue -> Cont 'CallByValue
  CLetR :: Env 'CallByValue -> Variable -> FlatTerm -> Cont 'CallByValue
        -> Cont 'CallByValue
  CConsApp :: Env 'CallByValue -> Variable -> [Value 'CallByValue] -> [FlatTerm]
           -> Cont 'CallByValue -> Cont 'CallByValue

instance Pretty (Cont strat) where
  pp CEmpty = "ε"
  pp (CPrompt c) = "CPrompt" <+> "•" <+> pp c
  pp (CForce c) = "CForce" <+> "•" <+> pp c
  pp (CRet v c) =  "CRet" <+> pp v <+> "•" <+> pp c
  pp (CAddL e t c) = "CAddL" <+> pp e <+> pp t <+> "•" <+> pp c
  pp (CAddR i c) = "CAddR" <+> show i <+> "•" <+> pp c
  pp (CCase e _ _ c) = "CCase" <+> pp e <+> "•" <+> pp c
  pp (CArg e t c) = "CArg" <+> pp e <+> pp t <+> "•" <+> pp c
  pp (CFun e x t c) = "CFun" <+> pp e <+> pp x <+> "•" <+> pp c
  pp (CDest h c) = "CDest" <+> pp h <+> "•" <+> pp c
  pp (CCoiterR _ _ _ c) = "CCoiterR" <+> "•" <+> pp c
  pp (CLetR _ _ _ c) = "CLetR" <+> "•" <+> pp c
  pp (CConsApp e cons _ _ c) = "CConsApp" <+> pp e <+> pp cons <+> "•" <+> pp c

data ControlTerm :: Strategy -> * where
  CtrlT :: FlatTerm -> ControlTerm strat
  CtrlE :: ControlTerm 'CallByValue
  -- ^ Instead of entering values like in call-by-name, call-by-value will push
  -- them on the continuation. This is similar to the CEK machine of Felleisen
  -- and Friedman.

instance Pretty (ControlTerm strat) where
  pp (CtrlT t) = pp t
  pp CtrlE = "●"

data MState strat
  = MState
  { env  :: Env strat
  , cont :: Cont strat
  , cterm :: ControlTerm strat }

instance Pretty (MState strat) where
  pp st = stringmconcat " ⎮ " [pp (env st),pp (cont st),pp (cterm st)] <> "\n"

interpPgm :: Strategy -> Bool -> Program FlatTerm -> Std (Int,FlatTerm)
interpPgm s debug t =
  case s of
    CallByName ->
      second (extractFinal SingCBN)
        <$> runMachine SingCBN debug 0 (MState emptyEnv CEmpty (CtrlT (pgmTerm $ t)))
    CallByValue ->
      second (extractFinal SingCBV)
        <$> runMachine SingCBV debug 0 (MState emptyEnv CEmpty (CtrlT (pgmTerm $ t)))

runMachine :: StratSingleton strat
           -> Bool
           -> Int
           -> MState strat
           -> Std (Int, MState strat)
runMachine strat debug i st =
  do { when debug (logStd (pp st))
     ; case finalState strat st of
         True  -> return (i,st)
         False -> step strat st >>= runMachine strat debug (i+1) }

finalState :: StratSingleton strat -> MState strat -> Bool
finalState SingCBN (MState _ CEmpty (CtrlT (FLit _))) = True
finalState SingCBN (MState _ CEmpty (CtrlT (FConsApp _ _))) = True
finalState SingCBV (MState _ (CRet v CEmpty) CtrlE) = True
finalState _ _ = False

extractFinal :: StratSingleton strat -> MState strat -> FlatTerm
extractFinal SingCBN (MState _ _ (CtrlT t)) = t
extractFinal SingCBV (MState _ (CRet v _) _) = valToFlatTerm v
extractFinal _ _ = error "extractFlatTerm"

step :: StratSingleton strat -> MState strat -> Std (MState strat)
step _ (MState e c (CtrlT (FPrompt t))) = return (MState e c (CtrlT t))
step _ (MState e c (CtrlT (FAnn t _))) = return (MState e c (CtrlT t))
step SingCBV (MState e c (CtrlT t))
  | Just val <- maybeCBVValue e t
  = return (MState emptyEnv (CRet val c) CtrlE)

-- Let expressions
step SingCBN (MState e c (CtrlT (FLet x t0 t1)))
  = return (MState (extendEnvVar x (VThunk e t0) e) c (CtrlT t1))
step SingCBV (MState e c (CtrlT (FLet x t0 t1)))
  = return (MState e (CLetR e x t1 c) (CtrlT t0))
step SingCBV (MState e (CRet val (CLetR e' x t1 c)) t0)
  = return (MState (extendEnvVar x val e') c (CtrlT t1))

-- Variables; entering them
step SingCBV (MState e c (CtrlT (FVar x))) =
  case lookup x (vars e) of
    Just (VFix t) -> return (MState e c (CtrlT t))
    Just val -> return (MState emptyEnv (CRet val c) CtrlE)
    Nothing -> failure ("<unbound variable>:" <+> pp x)
step SingCBN (MState e c (CtrlT (FVar x))) =
  case lookup x (vars e) of
    Just (VThunk e' t) -> return (MState e' c (CtrlT t))
    Just (VFix t) -> return (MState e c (CtrlT t))
    Nothing -> failure ("<unbound variable>:" <+> pp x)

-- Fix
step _ (MState e c (CtrlT (FFix x t))) =
  return (MState (extendEnvVar x (VFix t) e) c (CtrlT t))

-- Addition
step _ (MState e c (CtrlT (FAdd t0 t1))) = return (MState e (CAddL e t1 c) (CtrlT t0))
step SingCBN (MState _ (CAddL e t c) (CtrlT (FLit i)))
  = return (MState e (CAddR i c) (CtrlT t))
step SingCBN (MState e (CAddR i c) (CtrlT (FLit j)))
  = return (MState e c (CtrlT (FLit (i+j))))
step SingCBV (MState _ (CRet (VLit i) (CAddL e t c)) CtrlE)
  = return (MState e (CAddR i c) (CtrlT t))
step SingCBV (MState e (CRet (VLit j) (CAddR i c)) CtrlE)
  = return (MState e (CRet (VLit (i+j)) c) CtrlE)


-- Data
step _ (MState e c (CtrlT (FCase t0 b def))) =
  return (MState e (CCase e b def c) (CtrlT t0))
step SingCBN (MState e (CCase e' (FlatPatVar x,t0) _ c) (CtrlT t1)) =
  return (MState (extendEnvVar x (VThunk e t1) e') c (CtrlT t0))
step SingCBN (MState e (CCase e' (FlatPatCons cons xs,t0) (y,t1) c) (CtrlT (FConsApp cons' ts))) =
  case cons == cons' && length xs == length ts of
    True ->
      return (MState (extendManyEnvVar (zip xs (fmap (VThunk e) ts)) e') c (CtrlT t0))
    False ->
      return (MState (extendEnvVar y (VThunk e (FConsApp cons' ts)) e') c (CtrlT t1))

step SingCBV (MState e c (CtrlT (FConsApp cons []))) =
  return (MState e (CRet (VConsApp cons []) c) CtrlE)
step SingCBV (MState e c (CtrlT (FConsApp cons (t:ts)))) =
  return (MState e (CConsApp e cons [] ts c) (CtrlT t))
step SingCBV (MState _ (CRet val (CConsApp e cons vs ts c)) CtrlE) =
  return (MState emptyEnv (CConsApp e cons (val:vs) ts c) CtrlE)
step SingCBV (MState _ (CConsApp e cons vs (t:ts) c) CtrlE) =
  return (MState e (CConsApp e cons vs ts c) (CtrlT t))
step SingCBV (MState _ (CConsApp e cons vs [] c) CtrlE) =
  return (MState emptyEnv (CRet (VConsApp cons (reverse vs)) c) CtrlE)
step SingCBV (MState _ (CRet val (CCase e (FlatPatVar x, t) _ c)) CtrlE) =
  return (MState (extendEnvVar x val e) c (CtrlT t))
step SingCBV (MState _ (CRet (VConsApp cons vs) (CCase e' (FlatPatCons cons' xs,t0) (y,t1) c)) CtrlE) =
  case cons == cons' && length xs == length vs of
    True ->
      return (MState (extendManyEnvVar (zip xs vs) e') c (CtrlT t0))
    False ->
      return (MState (extendEnvVar y (VConsApp cons vs) e') c (CtrlT t1))

------------
-- CODATA --
------------

-- Applications
step _ (MState e c (CtrlT (FObsApp t0 t1))) =
  return (MState e (CArg e t0 c) (CtrlT t1))
step SingCBN (MState e (CArg e1 t1 c) (CtrlT (FFun x t))) =
  return (MState (extendEnvVar x (VThunk e1 t1) e) c (CtrlT t))

step SingCBV (MState _ (CRet (VFunClos e0 x t0) (CArg e1 t1 c)) CtrlE) =
  return (MState e1 (CFun e0 x t0 c) (CtrlT t1))
step SingCBV (MState _ (CRet val (CFun e x t c)) CtrlE)
  = return (MState (extendEnvVar x val e) c (CtrlT t))

-- General codata obs
step _ (MState e c (CtrlT (FObsDest h t)))
  = return (MState e (CDest h c) (CtrlT t))

step SingCBN (MState e (CDest h c) (CtrlT (FCoalt (h',t0) t1)))
 = case h == h' of
     True -> return (MState e c (CtrlT t0))
     False -> return (MState e (CDest h c) (CtrlT t1))

step SingCBV (MState _ (CRet (VCoalt e (h',t0) t1) (CDest h c)) CtrlE)
 = case h == h' of
     True -> return (MState e c (CtrlT t0))
     False -> return (MState e (CDest h c) (CtrlT t1))

-- Coiter codata
step SingCBN (MState e (CDest h c) (CtrlT (FStreamCoiter (x,t0) (y,t1) t2)))
  = case h of
      -- NOTA BENE: Here I just check that the first part of the destructor is
      -- 'Head' or 'Tail' since the renamer will create new names for these that
      -- have numbers at the end. This will break if a user defines a codata
      -- type with a destructor that begins with 'Head' or 'Tail', but is not
      -- the canonical stream one.
      Variable ('H':'e':'a':'d':_) ->
        return (MState (extendEnvVar x (VThunk e t2) e) c (CtrlT t0))
      Variable ('T':'a':'i':'l':_) ->
        return (MState (extendEnvVar y (VThunk e t2) e)
                       c
                       (CtrlT (FStreamCoiter (x,t0) (y,t1) t1)))
      _  -> failure $ "<observation error>: cannot observe" <+> pp h
step SingCBV (MState e c (CtrlT (FStreamCoiter b0 b1 t)))
  = return (MState e (CCoiterR e b0 b1 c) (CtrlT t))
step SingCBV (MState _ (CRet val (CCoiterR e' b0 b1 c)) CtrlE)
  = return (MState emptyEnv (CRet (VCoiter e' b0 b1 val) c) CtrlE)
step SingCBV (MState _ (CRet (VCoiter e' (x,t0) (y,t1) val) (CDest h c)) CtrlE)
  = case h of
      -- NOTA BENE: Here I just check that the first part of the destructor is
      -- 'Head' or 'Tail' since the renamer will create new names for these that
      -- have numbers at the end. This will break if a user defines a codata
      -- type with a destructor that begins with 'Head' or 'Tail', but is not
      -- the canonical stream one.
      Variable ('H':'e':'a':'d':_) ->
        return (MState (extendEnvVar x val e') c (CtrlT t0))
      Variable ('T':'a':'i':'l':_) ->
        return (MState (extendEnvVar y val e')
                       c
                       (CtrlT (FStreamCoiter (x,t0) (y,t1) t1)))
      _  -> failure $ "<observation error>: cannot observe" <+> pp h

-- A stuck program
step _ _ = failure "<stuck>"
