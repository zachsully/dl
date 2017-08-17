{-# LANGUAGE GADTs #-}
module DualLanguage where

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

data Type where
  Nat    :: Type
  Fun    :: Type -> Type -> Type
  TyVar  :: TyVariable -> Type
  TyApp  :: Type -> Type -> Type
  TyDecl :: Type
  deriving (Eq,Show)

{- A symbol introduced at the type level -}
newtype TySymbol = TySymbol String
  deriving (Eq,Show)

newtype TyVariable = TyVariable String
  deriving (Eq,Show)

data Polarity = Positive | Negative
  deriving (Eq,Show)

{- Decl introduce types, which can be eliminated with TyApp.
   The list of Data describes the set of term level ways to create an
   of this type -}
data Decl = Decl Polarity TySymbol [TyVariable] [Data]
  deriving (Eq,Show)

{- The polarity describes the nature of the Data parameters.
   If it is positive, then the list of Data corresponds to a disjoint union of
   injections into the new data type. E.g.

     data List a where
       Nil  :: List a
       Cons :: a -> List a -> List a

  If it is negative, then the list of Data corresponds to a product of
  projections out of the new data type. E.g.

    data Stream a where
      Head :: Stream a -> a
      Tail :: Stream a -> Stream a
-}

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------

data Term where
  Var :: Variable -> Term

  {- positive datum intro and elim -}
  Cons :: Symbol -> [Term] -> Term
  Case :: Term -> [(Pattern,Term)] -> Term

  Dest :: Symbol -> Term -> Term
  CoCase :: [(CoPattern,Term)] -> Term
  deriving (Eq,Show)

data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Symbol -> [Pattern] -> Pattern
  deriving (Eq,Show)

{- NOTE: we often use 'q' for a copattern variables -}
data CoPattern where
  QWild :: CoPattern
  QBox  :: CoPattern
  QDest :: Symbol -> CoPattern -> CoPattern
  QPat  :: CoPattern -> Pattern -> CoPattern
  deriving (Eq,Show)

{- Values are always positive data types. Also not that the are in weak head
   normal form, implying call-by-name -}
data Value where
  VCons :: Symbol -> [Term] -> Value
  deriving (Eq,Show)

data CoValue where
  VDest :: Symbol -> Term -> CoValue
  VCoCase :: [(CoPattern,Term)] -> CoValue
  deriving (Eq,Show)

{- Symbols are introduced in typing declarations -}
newtype Symbol = Symbol String
  deriving (Eq,Show)

{- Vars are introduced and consumed -}
newtype Variable = Variable String
  deriving (Eq,Show)

{- Data are added to a typing context as functions, in terms they are
   introductions to be eleminated by case statements -}
data Data = Data Symbol [Type]
  deriving (Eq,Show)


--------------------------------------------------------------------------------
--                           Primitive DataDecl                               --
--------------------------------------------------------------------------------

--------------
-- Positive --
--------------
unitDecl :: Decl
unitDecl = Decl Positive (TySymbol "Unit") [] [Data (Symbol "()") []]

pairDecl :: Decl
pairDecl = Decl Positive
                (TySymbol "Pair")
                [TyVariable "A",TyVariable "B"]
                [Data (Symbol "mkPair")
                      [TyVar (TyVariable "A")
                      ,TyVar (TyVariable "B")]]

eitherDecl :: Decl
eitherDecl = Decl Positive
                  (TySymbol "Either")
                  [TyVariable "A",TyVariable "B"]
                  [Data (Symbol "inl") [TyVar (TyVariable "A")]
                  ,Data (Symbol "inr") [TyVar (TyVariable "B")]]

listDecl :: Decl
listDecl = Decl Negative
                (TySymbol "List")
                [TyVariable "A"]
                [Data (Symbol "nil") []
                ,Data (Symbol "cons") [TyVar (TyVariable "A")
                                      ,TyApp (TyVar (TyVariable "List"))
                                             (TyVar (TyVariable "A"))]]

--------------
-- Negative --
--------------
negPairDecl :: Decl
negPairDecl = Decl Negative
                   (TySymbol "NegPair")
                   [TyVariable "A",TyVariable "B"]
                   [Data (Symbol "fst") [TyVar (TyVariable "A")]
                   ,Data (Symbol "snd") [TyVar (TyVariable "B")]]

streamDecl :: Decl
streamDecl = Decl Negative
                  (TySymbol "Stream")
                  [TyVariable "A"]
                  [Data (Symbol "head") []
                  ,Data (Symbol "tail") [TyApp (TyVar (TyVariable "Stream"))
                                               (TyVar (TyVariable "A"))]]

funDecl :: Decl
funDecl = Decl Negative
               (TySymbol "fun")
               [TyVariable "A",TyVariable "B"]
               [Data (Symbol "app") [TyVar (TyVariable "A")]]

--------------------------------------------------------------------------------
--                              Type Check                                    --
--------------------------------------------------------------------------------

type Sig = [Decl]
type Ctx = [(Variable,Type)]

-- Takes a term level symbol and returns the declaration containing the symbol
lookupSymbol :: Symbol -> Sig -> Maybe Decl
lookupSymbol sym [] = Nothing
lookupSymbol sym (d@(Decl _ _ _ dcs):ds) =
    case contains sym dcs of
      True -> Just d
      False -> lookupSymbol sym ds
  where contains s [] = False
        contains s ((Data s' _):dcs') =
          case s == s' of
            True -> True
            False -> contains s dcs'

-----------
-- infer --
-----------
infer :: Sig -> Ctx -> Term -> Type
infer s c (Cons sym ts) =
  case lookupSymbol sym s of
    Nothing -> error $ "no constructor: " ++ show sym
    Just (Decl _ _ _ _) ->
      let tys = map (infer s c) ts
      in error $ show tys

infer s c (Case t _) =
  let ty = infer s c t
  in undefined

infer _ _ (Dest _ _) = undefined
infer _ _ (CoCase _) = undefined


-----------
-- check --
-----------
check :: Sig -> Ctx -> Term -> Type -> Bool
check _ _ (Cons _ _) _  = undefined
check _ _ (Case _ _) _  = undefined
check _ _ (Dest _ _) _  = undefined
check _ _ (CoCase _) _  = undefined

--------------------------------------------------------------------------------
--                              Evaluation                                    --
--------------------------------------------------------------------------------

type Env = [(Variable,Term)]

{- An evaluation context for CoPatterns to match on -}
data QCtx where
  Box        :: QCtx
  Destructor :: QCtx -> Pattern -> QCtx
  Destructee :: Symbol -> QCtx -> QCtx

evalClosed :: Term -> Either CoValue Value
evalClosed = eval [] Box

eval :: Env -> QCtx -> Term -> Either CoValue Value
eval env qc (Var v) =
  case lookup v env of
    Just t -> eval env qc t
    Nothing -> error $ "unbound variable" ++ show v

eval _ _ (Cons k ts) = Right (VCons k ts)

eval env qc (Case t alts) =
  case eval env qc t of
    Right (VCons k ts) -> tryAlts (Cons k ts) alts
    _ -> error "case only operates on constructed values"
  where tryAlts :: Term -> [(Pattern,Term)] -> Either CoValue Value
        tryAlts _ [] = error "no matching alternative"
        tryAlts t' ((p,t''):alts') =
          case matchPattern t' p of
            Just subs -> eval (subs++env) qc t''
            Nothing -> tryAlts t' alts'

        matchPattern :: Term -> Pattern -> Maybe [(Variable,Term)]
        matchPattern t PWild = Just []
        matchPattern t (PVar v) = Just [(v,t)]
        matchPattern (Cons k ts) (PCons k' ps) =
          case k == k' of
            True -> let subs = map (\(t,p) -> matchPattern t p) (zip ts ps)
                    in foldr (\msub acc ->
                               case (msub,acc) of
                                 (_,Nothing) -> Nothing
                                 (Nothing,_) -> Nothing
                                 (Just as,Just bs) -> Just (as ++ bs)
                             ) (Just []) subs
            False -> Nothing
        matchPattern _ _ = Nothing



eval env qc (Dest s t) =
  let qc' = Destructee s qc in
  case eval env qc'  t of
    Left (VDest s' t') -> undefined
    Left (VCoCase coalts) -> tryCoAlts qc' coalts
    _ -> error "destructors must be applied to cocase"
  where tryCoAlts :: QCtx -> [(CoPattern,Term)] -> Either CoValue Value
        tryCoAlts _ [] = error "no copattern match"
        tryCoAlts qc ((q,t):coalts') =
          case matchCoPattern qc  q of
            True -> eval env qc t
            False -> tryCoAlts qc coalts'

        matchCoPattern :: QCtx -> CoPattern -> Bool
        matchCoPattern _   QWild = True
        matchCoPattern Box QBox  = True
        matchCoPattern (Destructee sym qctx) (QDest sym' q) =
          case sym == sym' of
            True -> matchCoPattern qctx q
            False -> False
        matchCoPattern _ _ = False

eval _ _ (CoCase coalts) = Left (VCoCase coalts)


--------------------------------------------------------------------------------
--                               Examples                                     --
--------------------------------------------------------------------------------

unit :: Term
unit = Cons (Symbol "()") []

pair1 :: Term
pair1 = Cons (Symbol "mkPair") [Cons (Symbol "mkPair") [unit,unit],unit]

pair2 :: Term
pair2 = Case pair1 [(PCons (Symbol "mkPair")
                           [PVar (Variable "x")
                           ,PVar (Variable "y")], Var (Variable "x"))]

lam :: Term
lam = CoCase [(QPat QWild (PVar (Variable "x"))
              ,Cons (Symbol "mkPair") [Var (Variable "x")
                                      ,Var (Variable "x")])]

negPair :: Term
negPair = CoCase [(QDest (Symbol "fst") QWild, unit)
                 ,(QDest (Symbol "snd") QWild, pair1)]

fstProj :: Term
fstProj = Dest (Symbol "fst") negPair

sndProj :: Term
sndProj = Dest (Symbol "snd") negPair
