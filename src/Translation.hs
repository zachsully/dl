module Translation where

import Data.Char (toLower)

import qualified DualSyn as D
import qualified HsSyn as H

translateProgram :: D.Program -> H.Program
translateProgram (D.Program decls term) =
  H.Program (map translateDecl decls) (translateTerm term)

translateDecl :: D.Decl -> H.Decl
translateDecl = undefined              

translateType :: D.Type -> H.Type
translateType = undefined

translateTerm :: D.Term -> H.Term
translateTerm = undefined
