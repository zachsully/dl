{-# LANGUAGE GADTs #-}
module DualSyn where

import Debug.Trace
import Control.Monad.State
import Data.Monoid ((<>))

import Utils

data Program
  = Pgm
  { pgmDecls :: [Decl]
  , pgmTerm  :: Term Pattern CoPattern}
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

ppType :: Type -> String
ppType TyInt = "Int"
ppType (TyArr a b) = ppType a <+> "->" <+> ppType b
ppType (TyVar v) = v
ppType (TyCons k) = k
ppType (TyApp a b) =  ppType a <+> ppType b

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
{- Terms are parameterized over the type of pattern and copattern. This is
   important because we only translate flat (co)patterns.
-}
data Term p q where
  -- ^ Number primitives
  Lit :: Int -> Term p q
  Add :: Term p q -> Term p q -> Term p q

  Var :: Variable -> Term p q
  Fix :: Variable -> Term p q -> Term p q
  App :: Term p q -> Term p q -> Term p q

  Cons :: Variable -> Term p q
  Case :: Term p q -> [(p,Term p q)] -> Term p q

  Dest :: Variable -> Term p q
  CoCase :: [(q,Term p q)] -> Term p q
  deriving (Eq,Show)

{- Vars are introduced and consumed by pattern matching within terms. -}
type Variable = String

{- `collectArgs` will recur down an application to find the constructor and its
   arguments -}
collectArgs :: Term p q -> Maybe (Variable,[Term p q])
collectArgs (App e t) = collectArgs e >>= \(k,ts) -> return (k,t:ts)
collectArgs (Cons k)  = return (k,[])
collectArgs _         = Nothing

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term p q]) -> Term p q
distributeArgs (k,ts) = foldl App (Cons k) ts


------------------
-- (Co)patterns --
------------------

data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Variable -> [Pattern] -> Pattern
  deriving (Eq,Show)

{- Atomic patterns are either wildcards or variables -}
data FlatP where
  FPWild :: FlatP
  FPVar  :: Variable -> FlatP
  FPCons :: Variable -> [Variable] -> FlatP
  deriving (Eq,Show)

{- NOTE: we often use 'q' for a copattern variables -}
data CoPattern where
  QHead :: CoPattern                          -- ^ the copattern matching the context
  QDest :: Variable -> CoPattern -> CoPattern -- ^ a specific destructor
  QPat  :: CoPattern -> Pattern -> CoPattern  -- ^ a copattern applied ot a pattern
  deriving (Eq,Show)

data FlatQ where
  FQHead :: FlatQ
  FQDest :: Variable -> FlatQ
  FQPat  :: FlatP    -> FlatQ
  deriving (Eq,Show)

--------------------------------------------------------------------------------
--                        Term Manipulations --
--------------------------------------------------------------------------------

innerMostCoPattern :: CoPattern -> CoPattern
innerMostCoPattern QHead           = QHead
innerMostCoPattern (QPat QHead p)  = QPat QHead p
innerMostCoPattern (QDest h QHead) = QDest h QHead
innerMostCoPattern (QDest _ q)     = innerMostCoPattern q
innerMostCoPattern (QPat q _)      = innerMostCoPattern q

{- `flattenPattern` will traverse a term, turning (co)case expressions with
   nested (co-)patterns in ones nesting (co)case expressions instead. This
   simplifies translation.

   An example of flattening a case:
   ```
   case (Pair (Pair 0 1) (Pair 1 2))
     { Pair (Pair w x) (Pair y z) -> w + x + y + z }
   ```
   ===>
   ```
   case (Pair 0 (Pair 1 2))
     { Pair p0 p1 ->
         case p0
           { Pair w x ->
               case p1
                { Pair y z -> w + x + y + z
                }
           }
     }
   ```

   An example of flattening a cocase:
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

fresh :: Variable -> State Int Variable
fresh v = do { n <- get
             ; put (succ n)
             ; return (v <> show n) }

flattenPatterns :: Term Pattern CoPattern -> Term FlatP FlatQ
flattenPatterns t = fst . runState (flattenPatterns' t) $ 0

flattenPatterns' :: Term Pattern CoPattern -> State Int (Term FlatP FlatQ)
flattenPatterns' (Lit i) = return (Lit i)
flattenPatterns' (Add a b) = Add <$> flattenPatterns' a <*> flattenPatterns' b
flattenPatterns' (Var v) = return (Var v)
flattenPatterns' (Fix v t) = Fix v <$> flattenPatterns' t
flattenPatterns' (App a b) = App <$> flattenPatterns' a <*> flattenPatterns' b
flattenPatterns' (Cons k) = return (Cons k)
flattenPatterns' (Dest h) = return (Dest h)
flattenPatterns' (Case t alts) = Case <$> flattenPatterns' t
                                      <*> mapM flattenAlt alts
  where flattenAlt :: (Pattern,Term Pattern CoPattern)
                   -> State Int (FlatP,Term FlatP FlatQ)
        flattenAlt (p,u) =
          do { u' <- flattenPatterns' u
             ; case p of
                 PWild -> return (FPWild, u')
                 PVar v -> return (FPVar v, u')
                 PCons k ps -> do { (vs,fs) <- unzip <$> mapM flattenPattern ps
                                  ; return (FPCons k vs, foldr ($) u' fs) }
             }

        flattenPattern :: Pattern
                       -> State Int (Variable, Term FlatP FlatQ -> Term FlatP FlatQ)
        flattenPattern PWild = do { v <- fresh "p"
                                  ; return (v, id) }
        flattenPattern (PVar v) = return (v,id)
        flattenPattern (PCons k ps) =
          do { v <- fresh "p"
             ; (vs,fs) <- unzip <$> mapM flattenPattern ps
             ; return ( v
                      , \e -> Case (Var v) [(FPCons k vs,foldr ($) e fs)])
             }

flattenPatterns' (CoCase coalts) =
  let maxD = maximum . map (getDepth . fst) $ coalts in
  do { error . show $ maxD }
  where getDepth :: CoPattern -> Int
        getDepth QHead       = 0
        getDepth (QDest _ q) = 1 + getDepth q
        getDepth (QPat q _)  = 1 + getDepth q

  -- where withInnerMostAndDepth :: (FlatQ -> Int -> r) -> CoPattern -> r
  --       withInnerMostAndDepth f q = wIMD f q 0
  --         where wIMD f D.QHead i -> f D.QHead i
  --               wIMD


--------------------------------------------------------------------------------
--                              Evaluation                                    --
--------------------------------------------------------------------------------
{- Evaluation is done over the more complex, recursive patterns and copatterns
-}
type Env = [(Variable,Term Pattern CoPattern)]

{- An evaluation context for CoPatterns to match on -}
data QCtx where
  Empty :: QCtx
  Push  :: Term Pattern CoPattern -> QCtx -> QCtx
  deriving (Show,Eq)

{- The machine returns results which can be of positive or negative types. We
   call this result instead of value (as is the common approach) because of the
   polarity of values. -}
data Result where
  RInt     :: Int -> Result
  RConsApp :: Variable -> [Term Pattern CoPattern] -> Result
  RDest    :: Variable -> Result
  RCoCase  :: [(CoPattern,Term Pattern CoPattern)] -> Result
  deriving (Eq,Show)

data Machine
  = Machine { run :: (Term Pattern CoPattern, QCtx, Env)
                  -> (Result, QCtx, Env)
            }

evalEmpty :: Term Pattern CoPattern -> Result
evalEmpty t = case run evalMachine (t,Empty,[]) of
                (r,Empty,_) -> r
                x -> error ("evaluation did not consume all of the evaluation context "
                           <> show x)

evalMachine :: Machine
evalMachine = Machine $ \(t,qc,env) ->
  trace ("---------------\nt: " <> show t <> "\nQ: " <> show qc <> "\n") $
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

    App t1 t2 -> run evalMachine (t1,Push t2 qc,env)
      -- case run evalMachine (t1,Push t2 qc,env) of
      --   (RConsApp k ts,qc',env')  -> (RConsApp k (t2:ts),qc',env')

      --   (RDest d,qc',env') -> run evalMachine (t2,Destructee d qc',env')

      --   (RCoCase coalts,qc',env') ->
      --     run evalMachine (CoCase coalts,Destructor qc' t2,env')

      --   t1' -> error $ show t1' ++ " is not a valid application term"

    Case t' alts ->
      let tryAlts :: Term Pattern CoPattern
                  -> [(Pattern,Term Pattern CoPattern)]
                  -> (Result, QCtx, Env)
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
      let tryCoAlts :: [(CoPattern,Term Pattern CoPattern)]
                    -> Maybe (Result, QCtx, Env)
          tryCoAlts [] = Nothing
          tryCoAlts ((q,t'):coalts') =
            case matchCoPattern qc (innerMostCoPattern q) of
              Just (qc',subs) -> Just (run evalMachine (t',qc',(subs++env)))
              Nothing -> tryCoAlts coalts'
      in case tryCoAlts coalts of
           Just r  -> r
           Nothing -> (RCoCase coalts,qc,env)

--------------------
-- Matching Rules --
--------------------

{- Takes a term and a pattern and returns a set of substitutions if it succeeds.
   Note that the set of substitutions can be empty. This is pretty standard. -}
matchPattern :: Term Pattern q -> Pattern -> Maybe [(Variable,Term Pattern q)]
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

matchCoPattern :: QCtx
               -> CoPattern
               -> Maybe (QCtx,[(Variable,Term Pattern CoPattern)])

{- Q , # -}
matchCoPattern qc QHead = Just (qc,[])

{- Q t , q p -}
matchCoPattern (Push t qc) (QPat q p) =
  do { (qc',subs1) <- matchCoPattern qc q
     ; subs2 <-  matchPattern t p
     ; return (qc',(subs1++subs2)) }

{- H Q , H q -}
matchCoPattern (Push (Dest s) qc) (QDest s' q) =
  case s == s' of
    True -> matchCoPattern qc q
    False -> Nothing

matchCoPattern _ _ = Nothing
