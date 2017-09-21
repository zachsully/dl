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

instance Pretty Program where
  pp pgm = (stringmconcat "\n\n" . fmap pp . pgmDecls $ pgm)
        <> "\n\n"
        <> (pp . pgmTerm $ pgm)

type Decl = Either NegativeTyCons PositiveTyCons

instance (Pretty a,Pretty b) => Pretty (Either a b) where
  pp _ = ""

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

instance Pretty NegativeTyCons where
  pp tc = "codata" <+> negTyName tc

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

instance Pretty PositiveTyCons where
  pp tc = "data" <+> posTyName tc

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
important because we only translate flat (co)patterns. -}
data Term p q where
  Let :: Variable -> Term p q -> Term p q -> Term p q

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

instance (Pretty p, Pretty q) => Pretty (Term p q) where
  ppInd _ (Lit i)         = show i
  ppInd i (Add a b)       = (parens . ppInd i $ a)
                        <+> "+"
                        <+> (parens . ppInd i $ b)
  ppInd _ (Var s)         = s
  ppInd i (Fix s t)       = "fix" <+> s <+> "in" <-> indent i (ppInd (i+1) t)
  ppInd i (Let s a b)     = "let" <+> s <+> "=" <+> ppInd (i+1) a
                        <-> indent i ("in" <+> ppInd (i+1) b)
  ppInd i (App a b)       = (parens . ppInd i $ a) <+> (parens . ppInd i $ b)
  ppInd _ (Cons k)        = k
  ppInd i (Case t alts)   = "case"
                        <+> ppInd i t
                        <-> indent (i+1) "{"
                        <-> ( stringmconcat ("\n" <> (indent i "| "))
                            . fmap (\(p,u) -> pp p <+> "->" <+> ppInd (i+2) u <> "\n")
                            $ alts)
                        <-> indent (i+1) "}"
  ppInd _ (Dest h)        = h
  ppInd i (CoCase [])     = "cocase {}"
  ppInd i (CoCase coalts) = "cocase"
                        <-> indent (i+1) "{ "
                        <>  ( stringmconcat ("\n" <> (indent (i+1) ", "))
                            . fmap (\(q,u) -> pp q <+> "->" <+> ppInd (i+2) u)
                            $ coalts)
                        <-> indent (i+1) "}"

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

{- Pattern -}
data Pattern where
  PWild :: Pattern
  PVar  :: Variable -> Pattern
  PCons :: Variable -> [Pattern] -> Pattern
  deriving (Eq,Show)

instance Pretty Pattern where
  pp PWild        = "_"
  pp (PVar s)     = s
  pp (PCons k ps) = k <+> (smconcat . fmap (parens . pp) $ ps)
-----------

{- Flat Patterns -}
data FlatP where
  FPWild :: FlatP
  FPVar  :: Variable -> FlatP
  FPCons :: Variable -> [Variable] -> FlatP
  deriving (Eq,Show)

instance Pretty FlatP where
  pp FPWild        = "_"
  pp (FPVar s)     = s
  pp (FPCons k vs) = k <+> smconcat vs
-----------


{- Copatterns -}
{- NOTE: we often use 'q' for a copattern variables -}
data CoPattern where
  QHead :: CoPattern                          -- ^ the copattern matching the context
  QDest :: Variable -> CoPattern -> CoPattern -- ^ a specific destructor
  QPat  :: CoPattern -> Pattern -> CoPattern  -- ^ a copattern applied ot a pattern
  deriving (Eq,Show)

instance Pretty CoPattern where
  pp QHead       = "#"
  pp (QDest h q) = h <+> (parens . pp $ q)
  pp (QPat q p)  = (parens . pp $ q) <+> (parens . pp $ p)
--------------

{- Flat Copatterns -}
data FlatQ where
  FQHead :: FlatQ
  FQDest :: Variable -> FlatQ
  FQPat  :: FlatP    -> FlatQ
  deriving (Eq,Show)

instance Pretty FlatQ where
  pp FQHead     = "#"
  pp (FQDest h) = h <+> "#"
  pp (FQPat p)  = "#" <+> pp p


--------------------------------------------------------------------------------
--                        Term Manipulations --
--------------------------------------------------------------------------------

{- Used in the context filling rules R-RecPat and R-RedDest, Takes a copattern and
returns (an optional new copattern with the inner most matchable pattern pulled
out and replace by head) and the inner most copattern -}

unplugCopattern :: CoPattern -> (Maybe CoPattern,CoPattern)
unplugCopattern QHead           = (Nothing, QHead)
unplugCopattern (QPat QHead p)  = (Nothing, (QPat QHead p))
unplugCopattern (QDest h QHead) = (Nothing, (QDest h QHead))
unplugCopattern (QDest h q)     = let (m,i) = unplugCopattern q in
                                  case m of
                                    Nothing -> (Just (QDest h QHead), i)
                                    Just q' -> (Just (QDest h q'), i)
unplugCopattern (QPat q p)      = let (m,i) = unplugCopattern q in
                                  case m of
                                    Nothing -> (Just (QPat QHead p), i)
                                    Just q' -> (Just (QPat q' p), i)

-- replace head with copattern in copattern
plugCopattern :: CoPattern -> CoPattern -> CoPattern
plugCopattern QHead       q' = q'
plugCopattern (QDest h q) q' = QDest h (plugCopattern q q')
plugCopattern (QPat q p)  q' = QPat (plugCopattern q q') p


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
flattenPatterns' (Let v a b) = Let v <$> flattenPatterns' a
                                     <*> flattenPatterns' b
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

-- R-QHead
flattenPatterns' (CoCase ((QHead,u):_)) = flattenPatterns' u
-- R-QPVar
flattenPatterns' (CoCase ((QPat QHead (PVar v),u):_)) =
  do { u' <- flattenPatterns' u
     ; return (CoCase [(FQPat (FPVar v), u')]) }
-- R-QPat
flattenPatterns' (CoCase ((QPat QHead p,u):coalts)) =
  do { v <- fresh "p"
     ; y <- fresh "y"
     ; let t = Case (Var v) [(p,u),(PVar y,CoCase coalts)]
     ; t' <- flattenPatterns' t
     ; return (CoCase [(FQPat (FPVar v), t')])
     }
-- R-QDest
flattenPatterns' (CoCase ((QDest h QHead,u):coalts)) =
  do { u' <- flattenPatterns' u
     ; coalts' <- flattenPatterns' (CoCase coalts)
     ; return (CoCase [(FQDest h,u'),(FQHead,coalts')])
     }
-- R-Rec
flattenPatterns' (CoCase ((q,u):coalts)) =
  flattenPatterns' (CoCase coalts) >>= \cocase' ->
  flattenPatterns' u >>= \u' ->
  case unplugCopattern q of
    (Just rest, QDest h QHead) ->
      do { u' <- flattenPatterns' ( CoCase [(rest,  u)
                                           ,(QHead, App (Dest h) (CoCase coalts))
                                           ]
                                  )
         ; return (CoCase [(FQDest h, u')
                          ,(FQHead,cocase')]) }
    (Just rest, QPat QHead p) ->
      do { x <- fresh "x"
         ; u' <- flattenPatterns' ( CoCase [(rest,  u)
                                           ,(QHead, App (CoCase coalts) (Var x))
                                           ]
                                  )
         ; return (CoCase [(FQPat (FPVar x), u')
                          ,(FQHead,cocase')]) }
    x -> error $ "todo{flattenPatterns'}" <+> show x

-- R-Empty is id
flattenPatterns' (CoCase []) = return (CoCase [])



--------------------------------------------------------------------------------
--                              Evaluation                                    --
--------------------------------------------------------------------------------
{- Evaluation is done over the more complex, recursive patterns and copatterns
-}
type Env = [(Variable,Term Pattern CoPattern)]

{- An evaluation context for CoPatterns to match on -}
data ObsCtx where
  ObsHead :: ObsCtx
  ObsApp  :: ObsCtx -> Term Pattern CoPattern -> ObsCtx
  ObsDest :: Variable -> ObsCtx -> ObsCtx
  deriving (Show,Eq)

{- The machine returns results which can be of positive or negative types. We
   call this result instead of value (as is the common approach) because of the
   polarity of values. -}
data Result where
  RInt       :: Int -> Result
  RConsApp   :: Variable -> [Term Pattern CoPattern] -> Result
  RDest      :: Variable -> Result
  RCoCase    :: [(CoPattern,Term Pattern CoPattern)] -> Result
  RMatchFail :: Result
  deriving (Eq,Show)

data Machine
  = Machine { run :: (Term Pattern CoPattern, ObsCtx, Env)
                  -> (Result, ObsCtx, Env)
            }

evalEmpty :: Term Pattern CoPattern -> Result
evalEmpty t = case run evalMachine (t,ObsHead,[]) of
                (r,ObsHead,_) -> r
                x -> error ("evaluation did not consume all of the evaluation context "
                           <> show x)

evalMachine :: Machine
evalMachine = Machine $ \(t,obsctx,env) ->
  trace (   "---------------\nt:"
        <+> pp t
        <>  "\nEnv:" <+> show env <> "\n") $
  case t of
    Let v a b -> trace "M-Let" $ run evalMachine (b,obsctx,(v,a):env)
    Lit i -> (RInt i,obsctx,env)
    Add t1 t2 ->
      case ( trace "M-Add1" $ run evalMachine (t1,obsctx,env)
           , trace "M-Add2" $ run evalMachine (t2,obsctx,env)) of
        ((RInt t1',_,_),(RInt t2',_,_)) -> (RInt (t1' + t2'),obsctx,env)
        _ -> error "both arguments to an addition must be integers"

    Var v ->
      case lookup v env of
        Just t' -> trace "M-Subs" $ run evalMachine (t',obsctx,env)
        Nothing -> error $ "unbound variable" ++ show v

    Fix x t' -> trace "M-Fix" $ run evalMachine (t',obsctx,(x,t):env)

    Cons k -> (RConsApp k [], obsctx, env)
    Dest h -> (RDest h, obsctx, env)

    App t1 t2 ->
      case trace "M-App1" $ run evalMachine (t1,obsctx,env) of
        (RConsApp k ts,obsctx',env')  -> (RConsApp k (t2:ts),obsctx',env')

        (RCoCase coalts,_,_) ->
          case matchCoalts (ObsApp obsctx t2) coalts of
            Just (u,obsctx',subs) -> trace "M-AppCoCaseMatch"
                                   $ run evalMachine (u,obsctx',subs <> env)
            Nothing -> (RMatchFail,obsctx,env)

        (RDest h,_,_) ->
          case trace "M-AppDest" $ run evalMachine (t2,obsctx,env) of
            (RCoCase coalts,_,_) ->
              case matchCoalts (ObsDest h obsctx) coalts of
                Just (u,obsctx',subs) -> trace "M-DestMatch"
                                       $ run evalMachine (u,obsctx',subs <> env)
                Nothing -> (RMatchFail,obsctx,env)

            (RMatchFail,_,_) -> (RMatchFail,obsctx,env)

            mach -> error ("Can only apply destructors to codata."
                          <-> " Given arugment:" <+> show mach)

        (RMatchFail,_,_) -> (RMatchFail,obsctx,env)

        t1' -> error $ show t1' ++ " is not a valid application term"

    Case t' alts ->
      let mt'' = case trace "M-Case" $ run evalMachine (t',obsctx,env) of
                   (RInt i,_,_)         -> Just (Lit i)
                   (RConsApp k ts,_,_)  -> Just (distributeArgs (k,ts))
                   (RDest h,_,_)        -> Just (Dest h)
                   (RCoCase coalts,_,_) -> Just (CoCase coalts)
                   (RMatchFail,_,_)     -> Nothing
      in case mt'' of
           Just t'' ->
             case matchAlts t'' alts of
               Just (u,subs) -> trace "M-CaseMatch"
                              $ run evalMachine (u,obsctx,subs <> env)
               Nothing -> (RMatchFail,obsctx,env)
           Nothing -> (RMatchFail,obsctx,env)

    -- if this is the head copattern then return righthand side
    CoCase coalts ->
      case matchCoalts obsctx coalts of
        Just (u,obsctx',subs) -> run evalMachine (u,obsctx',subs <> env)
        Nothing -> (RCoCase coalts,obsctx,env)

--------------------
-- Matching Rules --
--------------------

matchAlts
  :: Term Pattern CoPattern
  -> [(Pattern,Term Pattern CoPattern)]
  -> Maybe (Term Pattern CoPattern,[(Variable,Term Pattern CoPattern)])
matchAlts _ []           = Nothing
matchAlts r ((p,u):alts) =
  case matchPattern r p of
    Just subs -> Just (u,subs)
    Nothing   -> matchAlts r alts

{- Takes a term and a pattern and returns a set of substitutions if it succeeds.
   Note that the set of substitutions can be empty. This is pretty standard. -}
matchPattern
  :: Term Pattern q
  -> Pattern
  -> Maybe [(Variable,Term Pattern q)]
matchPattern _ PWild    = Just []
matchPattern t (PVar v) = Just [(v,t)]
matchPattern t (PCons k' ps) =
  do { (k,ts) <- collectArgs t
     ; case k == k' of
         True -> concat <$> mapM (\(t',p') -> matchPattern t' p') (zip ts ps)
         False -> Nothing
     }

{- Takes a copattern context and copattern and returns just a list of
substitutions if it succeeds. The reason there can be substitutions is because
patterns can be in copatterns which may bind variables. -}
matchCoalts
  :: ObsCtx
  -> [(CoPattern,Term Pattern CoPattern)]
  -> Maybe (Term Pattern CoPattern,ObsCtx,[(Variable,Term Pattern CoPattern)])
matchCoalts _      []             = Nothing
matchCoalts obsctx ((q,u):coalts) =
  trace (show obsctx <-> pp q) $
  case unplugCopattern q of
    (mrest,inner) ->
      case matchCoPattern obsctx inner of
        Just (obsctx',subs) ->
          case mrest of
            Just rest -> Just (CoCase [(rest, u)
                                      ,(QHead,CoCase coalts)]
                              ,obsctx'
                              ,subs)
            Nothing -> Just (u,obsctx',subs)
        Nothing -> matchCoalts obsctx coalts

{- returns the new observation context as well as a sequence of substitutions -}
matchCoPattern
  :: ObsCtx
  -> CoPattern
  -> Maybe (ObsCtx,[(Variable,Term Pattern CoPattern)])

{- Q , # -}
matchCoPattern obsctx QHead = Just (obsctx,[])

{- Q t , q p -}
matchCoPattern (ObsApp obsctx t) (QPat q p) =
  do { (obsctx',subs1) <- matchCoPattern obsctx q
     ; subs2 <-  matchPattern t p
     ; return (obsctx',(subs1++subs2)) }

{- H Q , H q -}
matchCoPattern (ObsDest h obsctx) (QDest h' q) =
  case h == h' of
    True -> matchCoPattern obsctx q
    False -> Nothing

matchCoPattern _ _ = Nothing
