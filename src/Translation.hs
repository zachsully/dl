{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

-- import Control.Arrow ((***))

import qualified DualSyn as D
import qualified HsSyn as Hs

{- A lot of the translation is boilerplate. We use separate syntax for DualSyn
   and HsSyn to make explicit what is happening even though the former is a
   subset of the latter.
-}

---------------
-- Top Level --
---------------

translateProgram :: D.Program -> Hs.Program
translateProgram dpgm = Hs.Pgm (map translateDecl . D.pgmDecls $ dpgm)
                               (translateTerm . D.pgmTerm $ dpgm)

translateDecl :: D.Decl -> Hs.DataTyCons
translateDecl (Right d) = Hs.DataTyCons (D.posTyName d)
                                        (D.posTyFVars d)
                                        (map translateInj . D.injections $ d)
translateDecl (Left d) = error "translateDecl{NegTyCons}"

translateInj :: D.Injection -> Hs.DataCon
translateInj dinj = Hs.DataCon (D.injName dinj) (translateType . D.injCod $ dinj)

-----------
-- Types --
-----------

translateType :: D.Type -> Hs.Type
translateType D.TyInt = Hs.TyInt
translateType (D.TyArr a b) = Hs.TyArr (translateType a) (translateType b)
translateType (D.TyVar v) = Hs.TyVar v
translateType (D.TyCons k) = Hs.TyCons k
translateType (D.TyApp a b) = Hs.TyApp (translateType a) (translateType b)

-----------
-- Terms --
-----------

translateTerm :: D.Term -> Hs.Term
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
