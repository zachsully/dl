{-# LANGUAGE GADTs #-}
module DualSyn where

import Debug.Trace

data Program
  = Pgm
  { pgmDecls :: [Decl]
  , pgmTerm  :: Term }
  deriving (Show,Eq)

type Decl = Either NegativeTyCons PositiveTyCons

declArity :: Decl -> Int
declArity (Left d)  = length . negTyFVars $ d
declArity (Right d) = length . posTyFVars $ d

{- There is a special polarity type because positive and negative types are
   declared with the same structure, but we still need to keep them separate. -}
data Polarity = Positive | Negative
  deriving (Eq,Show)

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

data Type where
  TyInt  :: Type
  TyArr  :: Type -> Type -> Type
  TyVar  :: TyVariable -> Type
  TyCons :: TyVariable -> Type
  TyApp  :: Type -> Type -> Type
  deriving (Eq,Show)

collectTyArgs :: Type -> Maybe (TyVariable,[Type])
collectTyArgs (TyApp e t) = collectTyArgs e >>= \(k,ts) -> return (k,t:ts)
collectTyArgs (TyCons k)  = return (k,[])
collectTyArgs _           = Nothing

distributeTyArgs :: (TyVariable,[Type]) -> Type
distributeTyArgs (k,ts) = foldl TyApp (TyCons k) ts

{- TyVariable are bound inside of the types in a declaration -}
type TyVariable = String

{- Intoduction of positive and negative types are done with NegativeTyCons and
   PositiveTyCons. These two are very similar. The notable difference is in
   projections and injections, where every projection must have domain and a
   codomain, injections may not take arguments. -}
data NegativeTyCons
  = NegTyCons
  { negTyName   :: TyVariable
  , negTyFVars  :: [TyVariable]
  , projections :: [Projection] }
  deriving (Eq,Show)

negTyArity :: NegativeTyCons -> Int
negTyArity = length . negTyFVars

data Projection
  = Proj
  { projName :: Variable
  , projDom  :: Type
  , projCod  :: Type   }
  deriving (Eq, Show)

data PositiveTyCons
  = PosTyCons
  { posTyName  :: TyVariable
  , posTyFVars :: [TyVariable]
  , injections :: [Injection]  }
  deriving (Eq, Show)

posTyArity :: PositiveTyCons -> Int
posTyArity = length . posTyFVars

data Injection
  = Inj
  { injName :: Variable
  , injCod  :: Type }
  deriving (Eq, Show)
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------

data Term where
  -- ^ Number primitives
  Lit :: Int -> Term
  Add :: Term -> Term -> Term

  Var :: Variable -> Term
  Fix :: Variable -> Term -> Term
  App :: Term -> Term -> Term

  Cons :: Variable -> Term
  Case :: Term -> [(Pattern,Term)] -> Term

  Dest :: Variable -> Term
  CoCase :: [(CoPattern,Term)] -> Term
  deriving (Eq,Show)

data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Variable -> [Pattern] -> Pattern
  deriving (Eq,Show)

{- NOTE: we often use 'q' for a copattern variables -}
data CoPattern where
  QHash  :: CoPattern                         -- ^ the copattern matching the context
  QDest :: Variable -> CoPattern -> CoPattern -- ^ a specific destructor
  QPat  :: CoPattern -> Pattern -> CoPattern  -- ^ a copattern applied ot a pattern
  deriving (Eq,Show)

{- The machine returns results which can be of positive or negative types. We
   call this result instead of value (as is the common approach) because of the
   polarity of values. -}
data Result where
  RInt     :: Int -> Result
  RConsApp :: Variable -> [Term] -> Result
  RDest    :: Variable -> Result
  RCoCase  :: [(CoPattern,Term)] -> Result
  deriving (Eq,Show)

{- Vars are introduced and consumed by pattern matching within terms. -}
type Variable = String


------------------------
-- Term Manipulations --
------------------------

{- `collectArgs` will recur down an application to find the constructor and its
   arguments -}
collectArgs :: Term -> Maybe (Variable,[Term])
collectArgs (App e t) = collectArgs e >>= \(k,ts) -> return (k,t:ts)
collectArgs (Cons k)  = return (k,[])
collectArgs _         = Nothing

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term]) -> Term
distributeArgs (k,ts) = foldl App (Cons k) ts


{- `flattenCopattern` will traverse a term, turning CoCases with nested
   co-patterns in ones nesting cocase expressions instead. For example,

   ```
   cocase { Fst # -> 0
          , Fst (Snd #) -> 1
          , Snd (Snd #) -> 2 }
   ```
   ===>
   ```
   cocase { Fst # -> 0
          , Snd # -> cocase { Fst # -> 1
                            , Snd # -> 2 } }
   ```
-}

flattenCoCase :: [(CoPattern,Term)] -> [(CoPattern,Term)]
flattenCoCase [] = []
flattenCoCase (coalt:coalts) =
  let coalt' = case coalt of
                 -- the aready flatten cases
                 (QHash            , _) -> coalt
                 (QDest _     QHash, _) -> coalt
                 (QPat  QHash _    , _) -> coalt

                 (QDest _     _    , _) -> error "flattenCoCase{}"
                 (QPat  _     _    , _) -> error "flattenCoCase{}"
  in coalt':(flattenCoCase coalts)

--------------------------------------------------------------------------------
--                              Evaluation                                    --
--------------------------------------------------------------------------------

type Env = [(Variable,Term)]

{- An evaluation context for CoPatterns to match on -}
data QCtx where
  Empty      :: QCtx
  Destructor :: QCtx -> Term -> QCtx
  Destructee :: Variable -> QCtx -> QCtx
  deriving (Show,Eq)

data Machine = Machine { run :: (Term, QCtx, Env) -> (Result, QCtx, Env) }

evalStart :: Term -> Result
evalStart t = case run evalMachine (t,Empty,[]) of
                (r,_,_) -> r

evalMachine :: Machine
evalMachine = Machine $ \(t,qc,env) ->
  trace (show (t,qc,env)) $
  case t of
    Lit i -> (RInt i,qc,env)
    Add t1 t2 ->
      case (run evalMachine (t1,qc,env), run evalMachine (t2,qc,env)) of
        ((RInt t1',_,_),(RInt t2',_,_)) -> (RInt (t1' + t2'),qc,env)
        _ -> error "both arguments to an addition must be integers"

    Var v ->
      case lookup v env of
        Just t' -> run evalMachine (t',qc,env)
        Nothing -> error $ "unbound variable" ++ show v

    Fix x t' -> run evalMachine (t',qc,(x,t):env)

    Cons k -> (RConsApp k [], qc, env)
    Dest d -> (RDest d, qc, env)

    App t1 t2 ->
      case run evalMachine (t1,qc,env) of
        (RConsApp k ts,qc',env')  -> (RConsApp k (t2:ts),qc',env')

        (RDest d,qc',env')        ->
          case run evalMachine (t2, qc, env) of
            (RCoCase coalts,_,_) ->
              run evalMachine (CoCase coalts,Destructee d qc',env')
            _ -> error "can only apply destructors to cocase"

        (RCoCase coalts,qc',env') ->
          run evalMachine (CoCase coalts,Destructor qc' t2,env')
        _ -> error $ show t1 ++ " is not a valid application term"

    Case t' alts ->
      let tryAlts :: Term -> [(Pattern,Term)] -> (Result, QCtx, Env)
          tryAlts _ [] = error "no matching alternative"
          tryAlts r ((p,t''):alts') =
            case matchPattern r p of
              Just subs -> run evalMachine (t'',qc,(subs++env))
              Nothing -> tryAlts r alts'
      in case run evalMachine (t',qc,env) of
           (RInt i,_,_)         -> tryAlts (Lit i) alts
           (RConsApp k ts,_,_)  -> tryAlts (distributeArgs (k,ts)) alts
           (RDest h,_,_)        -> tryAlts (Dest h) alts
           (RCoCase coalts,_,_) -> tryAlts (CoCase coalts) alts


    CoCase coalts ->
      let tryCoAlts :: [(CoPattern,Term)] -> Maybe (Result, QCtx, Env)
          tryCoAlts [] = Nothing
          -- tryCoAlts [] = error (concat ["no copattern context match:\nQ = "
          --                              ,show qc,"\nt = ",show t])
          tryCoAlts ((q,t'):coalts') =
            case matchCoPattern qc  q of
              Just (qc',subs) -> Just (run evalMachine (t',qc',(subs++env)))
              Nothing -> tryCoAlts coalts'
      in case tryCoAlts coalts of
           Just r  -> trace "fail comatch" r
           Nothing -> (RCoCase coalts,qc,env)

--------------------
-- Matching Rules --
--------------------

{- Takes a term and a pattern and returns a set of substitutions if it succeeds.
   Note that the set of substitutions can be empty. This is pretty standard. -}
matchPattern :: Term -> Pattern -> Maybe [(Variable,Term)]
matchPattern _ PWild    = Just []
matchPattern t (PVar v) = Just [(v,t)]
matchPattern t (PCons k' ps) =
  do { (k,ts) <- collectArgs t
     ; case k == k' of
         True -> concat <$> mapM (\(t',p') -> matchPattern t' p') (zip ts ps)
         False -> Nothing
     }

{- Takes a copattern context and copattern and returns just a list of
   substitutions if it succeeds. The reason there can be substitutions
   is because patterns can be in copatterns which may bind variables.

   [Problem] Consider the two instances of NegPair Int Int, which I (Zach) think
   should be equal. I give their traces as well in the context of the
   observation `fst (snd f)`:

   ```
   f1 = cocase { fst #       -> 1
               , fst (snd #) -> 2
               , snd (snd #) -> 3 }

   f2 = cocase { fst # -> 1
               , snd # -> cocase { fst # -> 2
                                 , snd # -> 3 }
               }
   ```

   0 : < fst (snd f1) , # >
   1 : < snd f1       , fst # >
   2 : < f1           , snd (fst #) >
   3 : 2

   0 : < fst (snd f2) , # >
   1 : < snd f2       , fst # >
   2 : < f2           , snd (fst #) >
     -- error : `snd #` does not match `snd (fst #)`

   Solution:

   Instead of having a copattern for matching the top of the context with
   `QWild` and a copattern to exactly match the remaining environment `QEmpty`,
   We will just use `QWild` which will be denoted hash `#`

   f2 = cocase { fst # -> 1
               , snd # -> cocase { fst # -> 2
                                 , snd # -> 3 }
               }

-}

matchCoPattern :: QCtx -> CoPattern -> Maybe (QCtx,[(Variable,Term)])

{- Q , # -}
matchCoPattern qc QHash = Just (qc,[])

{- Q t , q p -}
matchCoPattern (Destructor qc t) (QPat q p) =
  do { (qc',subs1) <- matchCoPattern qc q
     ; subs2 <-  matchPattern t p
     ; return (qc',(subs1++subs2)) }

{- H Q , H q -}
matchCoPattern (Destructee s qc) (QDest s' q) =
  case s == s' of
    True -> matchCoPattern qc q
    False -> Nothing

matchCoPattern _ _ = Nothing
