module Translation where

import qualified DualSyn as D
import qualified HsSyn as H

translateProgram :: D.Program -> H.Program
translateProgram (D.Program decls term) =
  H.Program (map translateDecl decls) (translateTerm term)

translateDecl :: D.Decl -> H.Decl
translateDecl decl =
  case D.polarity decl of
    D.Positive -> undefined
    D.Negative -> undefined

translateType :: D.Type -> H.Type
translateType D.TyInt = H.TyInt
translateType (D.TyArr a b) = H.TyArr (translateType a) (translateType b)
translateType (D.TyVar (D.TyVariable s)) = H.TyVar (H.TyVariable s)
translateType (D.TyCons _ _) = undefined

translateTerm :: D.Term -> H.Term
translateTerm = undefined
