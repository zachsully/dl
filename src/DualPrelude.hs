{- Prelude:
   This module contains a number of the standard data declarations including
   pairs and optional values.
-}
module DualPrelude where

import DualSyn
import VariableSyn
import TypeSyn

prelude :: [Decl]
prelude = [unitDecl,pairDecl,copairDecl]

--------------------------------------------------------------------------------
--                             Declarations                                   --
--------------------------------------------------------------------------------

--------------
-- Positive --
--------------

unitDecl :: Decl
unitDecl = Right
  (PosTyCons (Variable "1") []
    [Inj (Variable "()") (TyVar (Variable "1"))])

pairDecl :: Decl
pairDecl = Right
  (PosTyCons (Variable "Pair") [Variable "A",Variable "B"]
    [Inj (Variable "MkPair")
      (TyArr
       (TyVar (Variable "A"))
       (TyArr (TyVar (Variable "B"))
              (TyApp (TyApp (TyVar (Variable "Pair")) (TyVar (Variable "a")))
                     (TyVar (Variable "B")))))])

-- eitherDecl :: Decl
-- eitherDecl = Decl Positive
--                   (TySymbol "Either")
--                   [TyVariable "A",TyVariable "B"]
--                   [Data (Symbol "inl") (TyVar (TyVariable "A"))
--                   ,Data (Symbol "inr") (TyVar (TyVariable "B"))]

-- listDecl :: Decl
-- listDecl = Decl Negative
--                 (TySymbol "List")
--                 [TyVariable "A"]
--                 [Data (Symbol "nil") (TyCons (TySymbol "List")
--                                      [TyVar (TyVariable "A")])
--                 ,Data (Symbol "cons") (TyArr (TyVar (TyVariable "A"))
--                                              (TyCons (TySymbol "List")
--                                                      [TyVar (TyVariable "A")]))]

--------------
-- Negative --
--------------

copairDecl :: Decl
copairDecl = Left $
  NegTyCons (Variable "Copair") [Variable "A",Variable "B"]
    [Proj (Variable "Fst") (TyVar (Variable "A"))
    ,Proj (Variable "Snd") (TyVar (Variable "B"))]

-- streamDecl :: Decl
-- streamDecl = Decl Negative
--                   (TySymbol "Stream")
--                   [TyVariable "A"]
--                   [Data (Symbol "head") (TyCons (TySymbol "Stream")
--                                                 [TyVar (TyVariable "A")])
--                   ,Data (Symbol "tail") (TyCons (TySymbol "Stream")
--                                                 [TyVar (TyVariable "A")])]

-- funDecl :: Decl
-- funDecl = Decl Negative
--                (TySymbol "fun")
--                [TyVariable "A",TyVariable "B"]
--                [Data (Symbol "app") (TyVar (TyVariable "A"))]


--------------------------------------------------------------------------------
--                                  Terms                                     --
--------------------------------------------------------------------------------

unit :: Term
unit = Cons (Variable "()")

caseUnit :: Term
caseUnit = Case unit [(PCons (Variable "()") [] , Lit 42)]

pair0 :: Term
pair0 = distributeArgs (Variable "mkPair", [unit,unit] )

pair1 :: Term
pair1 = distributeArgs ( Variable "mkPair"
                       , [ distributeArgs ( Variable "mkPair", [ unit , unit ] )
                         , unit ] )

casePair1 :: Term
casePair1 = Case pair1 [( PCons (Variable "mkPair")
                                [PVar (Variable "x"),PVar (Variable "y")]
                        , Var (Variable "x"))]

lam :: Term
lam = CoCase [( QPat QHead (PVar (Variable "x"))
              , distributeArgs ((Variable "mkPair"),
                                [Var (Variable "x"),Var (Variable "x")]))]

app :: Term
app = App (CoCase [(QPat QHead (PVar (Variable "x"))
                   ,(Add (Var (Variable "x")) (Lit 20)))])
          (Lit 22)

foo1 :: Term
foo1 = CoCase [(QDest (Variable "Fst") QHead, Lit 1)
              ,(QDest (Variable "Fst") (QDest (Variable "Snd") QHead), Lit 2)
              ,(QDest (Variable "Snd") (QDest (Variable "Snd") QHead), Lit 3)]

foo2 :: Term
foo2 = CoCase [(QDest (Variable "Fst") QHead, Lit 1)
              ,(QDest (Variable "Snd") QHead,
                  CoCase [(QDest (Variable "Fst") QHead, Lit 2)
                         ,(QDest (Variable "Snd") QHead, Lit 3)])
              ]
zeros :: Term
zeros = Fix (Variable "s")
            (CoCase [ ( QDest (Variable "head") QHead , Lit 0 )
                    , ( QDest (Variable "Tail") QHead , (Var (Variable "s")))])

nats :: Term
nats = Fix (Variable "s")
           (CoCase [ (QDest (Variable "Head") QHead
                     , Lit 0 )
                   , (QDest (Variable "Tail") QHead
                     , Add (Lit 1)
                           (App (Dest (Variable "Head")) (Var (Variable "s"))))])
