{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

-- import Control.Arrow ((***))

import qualified DualSyn as D
import qualified HsSyn as H

{- A lot of the translation is boilerplate. We use separate syntax for DualSyn
   and HsSyn to make explicit what is happening even though the former is a
   subset of the latter.
-}

---------------
-- Top Level --
---------------

translateProgram :: D.Program -> H.Program
translateProgram (D.Pgm _ term) = H.Program [] (translateTerm term)
  -- H.Program (map translateDecl decls)

-- translateNegativeTyCons :: D. -> H.Decl
-- translateDecl decl =
--   case D.polarity decl of
--     D.Positive -> H.Decl (translateTySymbol (D.tySymbol decl))
--                          (map translateTyVariable (D.freeTyVars decl))
--                          (map translateData (D.datas decl))
--     D.Negative -> let num = length . D.datas $ decl in
--                   error "translateDecl{Negative}"

-- translateData :: D.Data -> H.Data
-- translateData (D.Data s ty) = H.Data (translateSymbol s) (translateType ty)

-----------
-- Types --
-----------

translateType :: D.Type -> H.Type
translateType = error "translateType"
-- translateType D.TyInt = H.TyInt
-- translateType (D.TyArr a b) = H.TyArr (translateType a) (translateType b)
-- translateType (D.TyVar v) = H.TyVar (translateTyVariable v)
-- translateType (D.TyCons s tys) = H.TyCons (translateTySymbol s)
--                                           (map translateType tys)

-----------
-- Terms --
-----------

translateTerm :: D.Term -> H.Term
translateTerm = error "translateTerm"
-- translateTerm (D.Lit i) = H.Lit i
-- translateTerm (D.Add a b) = H.Add (translateTerm a) (translateTerm b)
-- translateTerm (D.Var v) = H.Var (translateVariable v)
-- translateTerm (D.Fix v t) = H.Fix (translateVariable v) (translateTerm t)
-- translateTerm (D.Cons s ts) = H.Cons (translateSymbol s) (map translateTerm ts)
-- translateTerm (D.Case t alts) =
--   H.Case (translateTerm t) (map (translatePattern *** translateTerm) alts)

-- -- The interesting cases
-- translateTerm (D.App _ _) = error "translateTerm{D.App}"

-- translateTerm (D.Dest s t) =
--   H.Case (translateTerm t)
--          [(H.PCons (translateSymbol s) [],H.Var (H.Variable "x"))]

-- translateTerm (D.CoCase coalts) =
--   H.Cons (H.Symbol "mkCocase") (map (\(_,t) -> translateTerm t) coalts)

-- translatePattern :: D.Pattern -> H.Pattern
-- translatePattern D.PWild = H.PWild
-- translatePattern (D.PVar v) = H.PVar (translateVariable v)
-- translatePattern (D.PCons s ps) = H.PCons (translateSymbol s)
--                                           (map translatePattern ps)
