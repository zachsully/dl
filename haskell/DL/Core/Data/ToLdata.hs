module DL.Core.Data.ToLdata where

import DL.Core.Data.Syntax
import DL.Flat.Syntax

toLdata :: FlatTerm -> LData
toLdata (FLet v a b) = DLet v (toLdata a) (toLdata b)
toLdata (FVar s) = DVar s
toLdata (FFix v a) = DFix v (toLdata a)
toLdata (FAnn t ty) = DAnn (toLdata t) ty
toLdata (FLit i) = DLit i
toLdata (FAdd a b) = DAdd (toLdata a) (toLdata b)

toLdata (FConsApp v as) = undefined v as
toLdata (FCase a (p,b) (v,c)) = undefined a p b v c
toLdata (FCaseEmpty a) = undefined a
toLdata (FFun v a) = undefined v a
toLdata (FCoalt (v,a) b) = undefined v a b
toLdata (FShift v a) = undefined v a
toLdata FEmpty = undefined
toLdata (FPrompt a) = undefined a

toLdata (FObsApp o a) = undefined o a
toLdata (FObsDest o a) = undefined o a
toLdata (FObsCut o a) = undefined o a
