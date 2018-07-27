{- Prelude:
   This module contains a number of the standard data declarations including
   pairs and optional values.
-}
module DL.Prelude where

import DL.Syntax.Term
import DL.Syntax.Variable
import DL.Syntax.Type
import DL.Syntax.Top

prelude :: [Decl]
prelude = [unitDecl,pairDecl,eitherDecl,boolDecl,listDecl
          ,withDecl,streamDecl]

preludePgm :: Term -> Program Term
preludePgm t = Pgm prelude t

{-
PROBLEMA: Because the prelude is not in scope when parsing, constructors and
destructors are captured as just variables. So we need to traverse the AST to
replace the variable occurrences with Dest and Cons.
-}

--------------------------------------------------------------------------------
--                             Declarations                                   --
--------------------------------------------------------------------------------

--------------
-- Positive --
--------------

unitDecl :: Decl
unitDecl = mkDataDecl
  (PosTyCons (Variable "1") []
    [Inj (Variable "Unit") (TyCons (Variable "1"))])

pairDecl :: Decl
pairDecl = mkDataDecl
  (PosTyCons (Variable "Pair") [Variable "A",Variable "B"]
    [Inj (Variable "Pair")
      (TyArr
       (TyVar (Variable "A"))
       (TyArr (TyVar (Variable "B"))
              (TyApp (TyApp (TyCons (Variable "Pair")) (TyVar (Variable "A")))
                     (TyVar (Variable "B")))))])

listDecl :: Decl
listDecl = mkDataDecl
  (PosTyCons (Variable "List") [Variable "A"]
   [Inj (Variable "Nil")
     (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))
   ,Inj (Variable "Cons")
     (TyArr (TyVar (Variable "A"))
       (TyArr (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))
              (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))))]
  )

eitherDecl :: Decl
eitherDecl = mkDataDecl
  (PosTyCons (Variable "Either") [Variable "A",Variable "B"]
   [Inj (Variable "Left")
     (TyArr (TyVar (Variable "A"))
      (TyApp (TyApp (TyCons (Variable "Either")) (TyVar (Variable "A")))
        (TyVar (Variable "B"))))
   ,Inj (Variable "Right")
     (TyArr (TyVar (Variable "A"))
      (TyApp (TyApp (TyCons (Variable "Either")) (TyVar (Variable "A")))
        (TyVar (Variable "B"))))]
  )

boolDecl :: Decl
boolDecl = mkDataDecl
  (PosTyCons (Variable "Bool") []
    [Inj (Variable "True") (TyCons (Variable "Bool"))
    ,Inj (Variable "False") (TyCons (Variable "Bool"))]
  )

--------------
-- Negative --
--------------

withDecl :: Decl
withDecl = mkCodataDecl $
  NegTyCons (Variable "With") [Variable "A",Variable "B"]
    [Proj (Variable "Fst")
     (TyArr (TyApp (TyApp (TyCons (Variable "With")) (TyVar (Variable "A")))
               (TyVar (Variable "B")))
       (TyVar (Variable "A")))
    ,Proj (Variable "Snd")
     (TyArr (TyApp (TyApp (TyCons (Variable "With")) (TyVar (Variable "A")))
              (TyVar (Variable "B")))
       (TyVar (Variable "B")))]

streamDecl :: Decl
streamDecl = mkCodataDecl $
  (NegTyCons (Variable "Stream") [Variable "A"]
   [Proj (Variable "Head")
     (TyArr (TyApp (TyCons (Variable "Stream")) (TyVar (Variable "A")))
       (TyVar (Variable "A")))
   ,Proj (Variable "Tail")
     (TyArr (TyApp (TyCons (Variable "Stream")) (TyVar (Variable "A")))
       (TyApp (TyCons (Variable "Stream")) (TyVar (Variable "A"))))]
  )


--------------------------------------------------------------------------------
--                                  Terms                                     --
--------------------------------------------------------------------------------

zeros :: Term
zeros = Fix (Variable "s")
            (Coalts [ ( QDest (Variable "head") QHead , Lit 0 )
                    , ( QDest (Variable "Tail") QHead , (Var (Variable "s")))])

nats :: Term
nats = Fix (Variable "s")
           (Coalts [ (QDest (Variable "Head") QHead
                     , Lit 0 )
                   , (QDest (Variable "Tail") QHead
                     , Add (Lit 1)
                           (App (Dest (Variable "Head")) (Var (Variable "s"))))])
