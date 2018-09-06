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
unitDecl = DataDecl
  (PosTyCons (Variable "1") []
    [Inj (Variable "Unit") Nothing (TyCons (Variable "1"))])

pairDecl :: Decl
pairDecl = DataDecl
  (PosTyCons (Variable "Pair") [Variable "A",Variable "B"]
    [Inj (Variable "Pair") Nothing
      (TyArr
       (TyVar (Variable "A"))
       (TyArr (TyVar (Variable "B"))
              (TyApp (TyApp (TyCons (Variable "Pair")) (TyVar (Variable "A")))
                     (TyVar (Variable "B")))))])

listDecl :: Decl
listDecl = DataDecl
  (PosTyCons (Variable "List") [Variable "A"]
   [Inj (Variable "Nil") Nothing
     (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))
   ,Inj (Variable "Cons") Nothing
     (TyArr (TyVar (Variable "A"))
       (TyArr (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))
              (TyApp (TyCons (Variable "List")) (TyVar (Variable "A")))))]
  )

eitherDecl :: Decl
eitherDecl = DataDecl
  (PosTyCons (Variable "Either") [Variable "A",Variable "B"]
   [Inj (Variable "Left") Nothing
     (TyArr (TyVar (Variable "A"))
      (TyApp (TyApp (TyCons (Variable "Either")) (TyVar (Variable "A")))
        (TyVar (Variable "B"))))
   ,Inj (Variable "Right") Nothing
     (TyArr (TyVar (Variable "A"))
      (TyApp (TyApp (TyCons (Variable "Either")) (TyVar (Variable "A")))
        (TyVar (Variable "B"))))]
  )

boolDecl :: Decl
boolDecl = DataDecl
  (PosTyCons (Variable "Bool") []
    [Inj (Variable "True") Nothing (TyCons (Variable "Bool"))
    ,Inj (Variable "False") Nothing (TyCons (Variable "Bool"))]
  )

--------------
-- Negative --
--------------

withDecl :: Decl
withDecl = CodataDecl $
  NegTyCons (Variable "With") [Variable "A",Variable "B"]
    [Proj (Variable "Fst") Nothing
     (TyArr (TyApp (TyApp (TyCons (Variable "With")) (TyVar (Variable "A")))
               (TyVar (Variable "B")))
       (TyVar (Variable "A")))
    ,Proj (Variable "Snd") Nothing
     (TyArr (TyApp (TyApp (TyCons (Variable "With")) (TyVar (Variable "A")))
              (TyVar (Variable "B")))
       (TyVar (Variable "B")))]

streamDecl :: Decl
streamDecl = CodataDecl $
  (NegTyCons (Variable "Stream") [Variable "A"]
   [Proj (Variable "Head") Nothing
     (TyArr (TyApp (TyCons (Variable "Stream")) (TyVar (Variable "A")))
       (TyVar (Variable "A")))
   ,Proj (Variable "Tail") Nothing
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
