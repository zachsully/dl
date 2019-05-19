module DL.DMach.Translation
  (dmachCompile) where


import DL.Backend
import DL.General.Top
import DL.Flat.Syntax
import DL.DMach.Syntax
import DL.Utils.StdMonad hiding (fvs)
import DL.Utils.FreeVars

dmachCompile :: Backend FlatTerm
dmachCompile = Backend trans

trans :: Program FlatTerm -> DMach
trans t =
  case runStd . transTerm . pgmTerm $ t of
    Left  e -> error e
    Right a -> a

{- This pass also preforms A-normalization! -}
transTerm :: FlatTerm -> Std DMach
transTerm (FLet v a b) = DMLet v <$> transTerm a <*> transTerm b
transTerm (FVar v) = return (DMObs v DMOApp [])
transTerm (FFix v a) = DMFix v <$> transTerm a
transTerm (FAnn a _ty) = transTerm a
transTerm (FLit i) = return (DMLit i)
transTerm (FAdd a b) =
  do { aV <- freshVariable
     ; a' <- transTerm a
     ; bV <- freshVariable
     ; b' <- transTerm b
     ; return (DMLet aV a' (DMLet bV b' (DMAdd aV bV))) }
transTerm (FConsApp v as) =
  do { binds <- mapM (\a -> (,) <$> freshVariable <*> transTerm a) as
     ; return (dmLets binds (DMConsApp v (map fst binds))) }
transTerm (FCase _a _alt _def) = undefined
transTerm (FCaseEmpty _a) = undefined
transTerm (FFun v a) =
  do { a' <- transTerm a
     ; return (DMClosure (fvs a') (DMLam [v] a')) }
transTerm (FCoalt (_h,_u) _t) = undefined
transTerm (FShift _v _a) = undefined
transTerm FEmpty = return DMFail
transTerm (FPrompt _a) = undefined
transTerm (FObsApp a b) =
  do { a' <- transTerm a
     ; aV <- freshVariable
     ; b' <- transTerm b
     ; bV <- freshVariable
     ; return (DMLet aV a' (DMLet bV b' (DMObs aV DMOApp [bV]))) }
transTerm (FObsDest h a) =
  do { a' <- transTerm a
     ; aV <- freshVariable
     ; return (DMLet aV a' (DMObs aV (DMODest h) [])) }
transTerm (FObsCut _v _a) = undefined
