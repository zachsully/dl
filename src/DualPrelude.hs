{- Prelude:
   This module contains a number of the standard data declarations including
   pairs and optional values.
-}
module DualPrelude where

import DualSyn

--------------------------------------------------------------------------------
--                             Declarations                                   --
--------------------------------------------------------------------------------

--------------
-- Positive --
--------------

-- unitDecl :: Decl
-- unitDecl = Decl Positive (TySymbol "Unit") []
--                          [Data (Symbol "()") (TyVar (TyVariable "Unit"))]

-- pairDecl :: Decl
-- pairDecl = Decl Positive
--                 (TySymbol "Pair")
--                 [TyVariable "A",TyVariable "B"]
--                 [Data (Symbol "mkPair")
--                       (TyArr (TyVar (TyVariable "A"))
--                              (TyVar (TyVariable "B")))]

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

-- negPairDecl :: Decl
-- negPairDecl = Decl Negative
--                    (TySymbol "NegPair")
--                    [TyVariable "A",TyVariable "B"]
--                    [Data (Symbol "fst") (TyVar (TyVariable "A"))
--                    ,Data (Symbol "snd") (TyVar (TyVariable "B"))]

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
unit = Cons "()"

caseUnit :: Term
caseUnit = Case unit [(PCons "()" [] , Lit 42)]

pair0 :: Term
pair0 = distributeArgs ( "mkPair", [unit,unit] )

pair1 :: Term
pair1 = distributeArgs ( "mkPair"
                       , [ distributeArgs ( "mkPair", [ unit , unit ] )
                         , unit ] )

casePair1 :: Term
casePair1 = Case pair1 [( PCons "mkPair" [PVar "x",PVar "y"]
                        , Var "x")]

lam :: Term
lam = CoCase [( QPat QHash (PVar "x")
              , distributeArgs ("mkPair",[Var "x",Var "x"]))]

app :: Term
app = App (CoCase [(QPat QHash (PVar "x")
                   ,(Add (Var "x") (Lit 20)))])
          (Lit 22)

foo1 :: Term
foo1 = CoCase [(QDest "Fst" QHash, Lit 1)
              ,(QDest "Fst" (QDest "Snd" QHash), Lit 2)
              ,(QDest "Snd" (QDest "Snd" QHash), Lit 3)]

foo2 :: Term
foo2 = CoCase [(QDest "Fst" QHash, Lit 1)
              ,(QDest "Snd" QHash,
                  CoCase [(QDest "Fst" QHash, Lit 2)
                         ,(QDest "Snd" QHash, Lit 3)])
              ]
zeros :: Term
zeros = Fix "s"
            (CoCase [ ( QDest "head" QHash , Lit 0 )
                    , ( QDest "Tail" QHash , (Var "s"))])

nats :: Term
nats = Fix "s"
           (CoCase [ (QDest "Head" QHash
                     , Lit 0 )
                   , (QDest "Tail" QHash
                     , Add (Lit 1)
                           (App (Dest "Head") (Var "s")))])
