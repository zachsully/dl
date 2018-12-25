module DL.Flat.ToLcodata
  (toLcodata) where

import Control.Monad.State
import Data.Map
import DL.General.Variable
import DL.Core.Codata.Syntax
import DL.Flat.Syntax
import DL.Utils.StdMonad

type CM a = StateT (Map Variable Variable) Std a

lookupCons :: Variable -> CM Variable
lookupCons k =
  do { s <- get
     ; return (undefined k s) }

toLcodata :: FlatTerm -> CM LCodata
toLcodata (FLet v a b) = CLet v <$> toLcodata a <*> toLcodata b
toLcodata (FVar v) = return (CVar v)
toLcodata (FFix v a) = CFix v <$> toLcodata a
toLcodata (FAnn a ty) = CAnn <$> toLcodata a <*> return ty

toLcodata (FLit i) = return (CLit i)
toLcodata (FAdd a b) = CAdd <$> toLcodata a <*> toLcodata b

toLcodata (FConsApp k as) =
  do { h   <- lookupCons k
     ; as' <- mapM toLcodata as
     ; v   <- lift freshVariable
     ; return (CCoalt (h,CFun v (capps (CObsDest k (CVar v)) as')) cfail) }
toLcodata (FCase a b c) =
  do { a' <- toLcodata a
     ; undefined a' b c }
toLcodata (FCaseEmpty _) = return cfail

toLcodata (FFun v a) = CFun v <$> toLcodata a
toLcodata (FCoalt (v,a) b) =
  do { a' <- toLcodata a
     ; CCoalt (v,a') <$> toLcodata b }
toLcodata (FShift v a) = CShift v <$> toLcodata a
toLcodata FEmpty = return CEmpty
toLcodata (FPrompt a) = CPrompt <$> toLcodata a

toLcodata (FObsApp a b) = CObsApp <$> toLcodata a <*> toLcodata b
toLcodata (FObsDest v a) = CObsDest v <$> toLcodata a
toLcodata (FObsCut v a) = CObsCut v <$> toLcodata a
