module DL.Flat.ToLdata where

import DL.Core.Data.Syntax
import DL.Flat.Syntax

toLdata :: FlatTerm -> LData
toLdata (FLet v a b) = DLet v (toLdata a) (toLdata b)
toLdata (FVar s) = DVar s
toLdata (FFix v a) = DFix v (toLdata a)
toLdata (FAnn t ty) = DAnn (toLdata t) ty

toLdata (FLit i) = DLit i
toLdata (FAdd a b) = DAdd (toLdata a) (toLdata b)

toLdata (FConsApp v as) = DConsApp v (fmap toLdata as)
toLdata (FCase a (p,b) (v,c))
  = DCase (toLdata a) (p, toLdata b) (v, toLdata c)
toLdata (FCaseEmpty a) = DCaseEmpty (toLdata a)

toLdata (FFun v a) = DFun v (toLdata a)
toLdata (FCoalt (v,a) b) = undefined v a b
toLdata (FShift v a) = undefined v a
toLdata FEmpty = undefined
toLdata (FPrompt a) = undefined a

toLdata (FObsApp a b) = DApp (toLdata a) (toLdata b)
toLdata (FObsDest o a) = undefined o a
toLdata (FObsCut o a) = undefined o a
toLdata (FStreamCoiter _ _ _) = error "toLdata{FStreamCoiter _ _ _}"
