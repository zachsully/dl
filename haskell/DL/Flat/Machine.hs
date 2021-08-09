{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, AllowAmbiguousTypes #-}
module DL.Flat.Machine where

import DL.Utils.StdMonad
import DL.Utils.Pretty
import DL.Flat.Syntax
import DL.General.Top
import DL.General.Variable
import DL.General.Strategy

--------------------------------------------------------------------------------
--                            Machine Parts                                   --
--------------------------------------------------------------------------------

type family Value (s :: Strategy) :: * where
  Value 'CallByName  = CBNValue
  Value 'CallByValue = CBVValue

data CBVValue :: * where
  VNum :: Int -> CBVValue
  VLam :: Variable -> FlatTerm -> CBVValue
  deriving Eq

instance Pretty CBVValue where
  pp = pp . toFlatTerm

toFlatTerm :: CBVValue -> FlatTerm
toFlatTerm (VNum i) = FLit i
toFlatTerm (VLam v t) = FFun v t

mkCBVValue :: FlatTerm -> Either CBVValue FlatTerm
mkCBVValue (FLit i)   = Left (VNum i)
mkCBVValue (FFun v t) = Left (VLam v t)
mkCBVValue t = Right t

data CBNValue :: * where
  NClos :: Env CBNValue -> FlatTerm -> CBNValue
  deriving Eq

instance Pretty CBNValue where
  pp (NClos _ t) = "{ # ->" <+> pp t <+> "}"

------------------------
-- Continuation Stuff --
------------------------
data Continuation :: Strategy -> * where
  -- universal
  KEmpty  :: Continuation s
  KAddL   :: Env (Value s) -> FlatTerm -> Continuation s -> Continuation s
  KAddR   :: Int -> Continuation s -> Continuation s
  KArg    :: Env (Value s) -> FlatTerm -> Continuation s -> Continuation s

  -- call-by-value specific
  KVApp   :: Env (Value 'CallByValue)
          -> Variable
          -> FlatTerm
          -> Continuation 'CallByValue
          -> Continuation 'CallByValue
  KVConsApp :: Variable
            -> [CBVValue]
            -> [FlatTerm]
            -> Continuation 'CallByValue
            -> Continuation 'CallByValue

instance Pretty (Continuation s) where
  pp KEmpty = "#"
  pp (KAddL _ t k) = "AddL" <+> pp t <+> parens (pp k)
  pp (KAddR i k) = "AddR" <+> show i <+> parens (pp k)
  pp (KArg _ t k) = "Arg" <+> parens (pp t) <+> parens (pp k)

  pp (KVApp _ v t k) = "CBVApp" <+> pp (FFun v t) <+> parens (pp k)
  pp (KVConsApp c vals args k)
    = "CBVConsApp" <+> pp c
    <+> show (fmap pp vals) <+> show (fmap pp args) <+> pp k

instance Eq (Continuation s) where
  KEmpty == KEmpty = True
  (KAddL _env0 t0 k0) == (KAddL _env1 t1 k1)
    = t0 == t1 && k0 == k1
  (KAddR i0 k0) == (KAddR i1 k1) = i0 == i1 && k0 == k1
  (KArg _ t0 k0) == (KArg _ t1 k1) = t0 == t1 && k0 == k1
  _ == _ = False

-----------------------
-- Environment Stuff --
-----------------------
data Env a :: * where
  Env :: [(Variable,a)] -> Env a

lookupEnv :: Env a -> Variable -> Std a
lookupEnv (Env assoc) v =
  case lookup v assoc of
    Just a  -> return a
    Nothing -> failure (mkRed "<unbound var>" <+> pp v)

emptyEnv :: Env a
emptyEnv = Env []

extendEnv :: Env a -> Variable -> a -> Env a
extendEnv (Env assoc) v a = Env ((v,a):assoc)

instance Eq a => Eq (Env a) where
  (Env assoc0) == (Env assoc1) = assoc0 == assoc1

--------------------------------------------------------------------------------
--                         Machine definition                                 --
--------------------------------------------------------------------------------
data MachineState (strat :: Strategy) :: * where
  MS :: StratSingleton strat
     -> Env (Value strat)
     -> FlatTerm
     -> Continuation strat
     -> MachineState strat

projTerm :: MachineState s -> FlatTerm
projTerm (MS _ _ t _) = t

projCont :: MachineState s -> Continuation s
projCont (MS _ _ _ k) = k

projStratSing :: MachineState s -> StratSingleton s
projStratSing (MS s _ _ _) = s

instance Eq (MachineState s) where
  (MS s0 _env0 t0 k0) == (MS s1 _env1 t1 k1)
    = s0 == s1 && t0 == t1 && k0 == k1

instance Pretty (MachineState s) where
  pp ms = "\nstrategy:" <+> pp (projStratSing ms)
          <-> "\nterm:"
          <-> pp (projTerm ms)
          <-> "\ncont:"
          <-> pp (projCont ms)

isFinalState :: MachineState s -> Bool
isFinalState (MS s _ t KEmpty) = isValue s t
isFinalState _ = False

isValue :: StratSingleton s -> FlatTerm -> Bool
isValue s       (FAnn t _)        = isValue s t
isValue _       (FLit _)          = True
isValue SingCBN (FConsApp _ _)    = True
isValue SingCBV (FConsApp _ args) = all (isValue SingCBV) args
isValue _       (FFun _ _)        = True
isValue _       (FCoalt _ _)      = True
isValue _       (FShift _ _)      = True
isValue _       FEmpty            = True
isValue _       (FPrompt _)       = False
isValue _       _                 = False

runMachine ::  MachineState s -> Std (MachineState s)
runMachine ms =
  do { logStd (mkBf "new state:" <-> pp ms)
     ; ms' <- stepMachineState ms
     ; case isFinalState ms' of
         True  -> return ms'
         False ->
           case ms' == ms of
             True  -> failure (mkRed "<machine loop>" <+> mkBf "final machine state:" <-> pp ms')
             False -> runMachine ms'
     }


runPgm :: Strategy -> Program FlatTerm -> Std FlatTerm
runPgm CallByName t
  = finalizeCBN <$> runMachine (MS SingCBN emptyEnv (pgmTerm t) KEmpty)
runPgm CallByValue t
  = finalizeCBV <$> runMachine (MS SingCBV emptyEnv (pgmTerm t) KEmpty)

finalizeCBN :: MachineState 'CallByName -> FlatTerm
finalizeCBN (MS _ (Env assoc) e _) =
  foldr (\(v,NClos _ a) t' -> substFlatTerm v a t') e assoc

finalizeCBV :: MachineState 'CallByValue -> FlatTerm
finalizeCBV (MS _ (Env assoc) e _) =
  foldr (\(v,val) t' -> substFlatTerm v (toFlatTerm val) t') e assoc


--------------------------------------------------------------------------------
--                         Operational Rules                                  --
--------------------------------------------------------------------------------
stepMachineState :: MachineState s -> Std (MachineState s)
stepMachineState (MS SingCBN env (FVar v) k)
  = lookupEnv env v >>= \(NClos env' t) -> return (MS SingCBN env' t k)
stepMachineState (MS SingCBV env (FVar v) k)
  = lookupEnv env v >>= \val -> return (MS SingCBV env (toFlatTerm val) k)

-- addition
stepMachineState (MS s env (FAdd left right) k)
  = return (MS s env left (KAddL env right k))
stepMachineState (MS s _ (FLit i) (KAddL env right k))
  = return (MS s env right (KAddR i k))
stepMachineState (MS s env (FLit i) (KAddR j k))
  = return (MS s env (FLit (i+j)) k)

------------------
-- applications --
------------------
stepMachineState (MS s env (FObsApp arg fun) k)
  = return (MS s env fun (KArg env arg k))

stepMachineState (MS SingCBN env (FFun v t) (KArg aenv arg k))
  = return (MS SingCBN (extendEnv env v (NClos aenv arg)) t k)

stepMachineState (MS SingCBV env (FFun v t) (KArg aenv arg k))
  = return (MS SingCBV aenv arg (KVApp env v t k))
stepMachineState (MS SingCBV env t (KVApp benv v body k))
  = case mkCBVValue t :: Either CBVValue FlatTerm of
      Left val -> return (MS SingCBV (extendEnv benv v val) body k)
      Right t' -> return (MS SingCBV env t' (KVApp benv v body k))

-- Evaluate constructor args in call-by-value
stepMachineState (MS SingCBV env (FConsApp cons (arg:args)) k)
  = case isValue SingCBV (FConsApp cons (arg:args)) of
      True  -> return (MS SingCBV env (FConsApp cons (arg:args)) k)
      False -> return (MS SingCBV env arg (KVConsApp cons [] args k))
stepMachineState (MS SingCBV env t (KVConsApp cons vals (arg:args) k))
  = case mkCBVValue t :: Either CBVValue FlatTerm of
      Left val -> return (MS SingCBV env arg (KVConsApp cons (val:vals) args k))
      Right t' -> return (MS SingCBV env t' (KVConsApp cons vals (arg:args) k))
stepMachineState (MS SingCBV env t (KVConsApp cons vals [] k))
  = case mkCBVValue t :: Either CBVValue FlatTerm of
      Left val -> return (MS SingCBV env (FConsApp cons (fmap toFlatTerm (val:vals))) k)
      Right t' -> return (MS SingCBV env t' (KVConsApp cons vals [] k))

-- control
stepMachineState (MS s env (FPrompt t) k)
  = return (MS s env t k)

-- undefined cases
stepMachineState ms = return ms
