{-# LANGUAGE GADTs #-}
module DualSyn where

import Debug.Trace
import Control.Monad.State
import Data.Monoid ((<>))

import Utils

data Program t
  = Pgm
  { pgmDecls :: [Decl]
  , pgmTerm  :: t }
  deriving (Show,Eq)

instance Pretty t => Pretty (Program t) where
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
data Term where
  Let :: Variable -> Term -> Term -> Term

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

instance Pretty Term where
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
collectArgs :: Term -> Maybe (Variable,[Term])
collectArgs (App e t) = collectArgs e >>= \(k,ts) -> return (k,t:ts)
collectArgs (Cons k)  = return (k,[])
collectArgs _         = Nothing

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term]) -> Term
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

flatten :: Term -> FlatTerm
flatten t = fst . runState (flatten' t) $ 0

flatten' :: Term -> State Int FlatTerm
flatten' (Let v a b) =
  FLet v <$> flatten' a <*> flatten' b
flatten' (Lit i) = return (FLit i)
flatten' (Add a b) = FAdd <$> flatten' a <*> flatten' b
flatten' (Var v) = return (FVar v)
flatten' (Fix v t) = FFix v <$> flatten' t
flatten' (App a b) = FApp <$> flatten' a <*> flatten' b
flatten' (Cons k) = return (FCons k)
flatten' (Dest h) = return (FDest h)
flatten' (Case t alts) =
  FCase <$> flatten' t <*> (flattenAlt . head $ alts) <*> return FFail
  where flattenAlt :: (Pattern,Term) -> State Int (FlatPattern,FlatTerm)
        flattenAlt (p,u) =
          do { u' <- flatten' u
             ; case p of
                 PVar v -> return (FlatPatVar v, u')
                 PCons k ps -> do { (vs,fs) <- unzip <$> mapM flattenPattern ps
                                  ; return (FlatPatCons k vs, foldr ($) u' fs) }
             }

        flattenPattern :: Pattern
                       -> State Int (Variable, FlatTerm -> FlatTerm)
        flattenPattern (PVar v) = return (v,id)
        flattenPattern (PCons k ps) =
          do { v <- fresh "p"
             ; (vs,fs) <- unzip <$> mapM flattenPattern ps
             ; return ( v
                      , \e -> FCase (FVar v)
                                    (FlatPatCons k vs,foldr ($) e fs)
                                    FFail)
             }
flatten' (CoCase ((QHead,u):_)) = flatten' u    -- R-QHead
flatten' (CoCase ((QPat QHead (PVar v),u):_)) = -- R-QPVar
  do { u' <- flatten' u
     ; return (FCoCase (FlatCopPat (FlatPatVar v), u') FFail) }
-- -- R-QPat
-- flatten' (CoCase ((QPat QHead p,u):coalts)) =
--   do { v <- fresh "p"
--      ; y <- fresh "y"
--      ; let t = Case (Var v) [(p,u),(PVar y,CoCase coalts)]
--      ; t' <- flatten' t
--      ; return (CoCase [(FQPat (FPVar v), t')])
--      }
-- -- R-QDest
-- flatten' (CoCase ((QDest h QHead,u):coalts)) =
--   do { u' <- flatten' u
--      ; coalts' <- flatten' (CoCase coalts)
--      ; return (CoCase [(FQDest h,u'),(FQHead,coalts')])
--      }
-- -- R-Rec
-- flatten' (CoCase ((q,u):coalts)) =
--   flatten' (CoCase coalts) >>= \cocase' ->
--   flatten' u >>= \u' ->
--   case unplugCopattern q of
--     (Just rest, QDest h QHead) ->
--       do { u' <- flatten' ( CoCase [(rest,  u)
--                                            ,(QHead, App (Dest h) (CoCase coalts))
--                                            ]
--                                   )
--          ; return (CoCase [(FQDest h, u')
--                           ,(FQHead,cocase')]) }
--     (Just rest, QPat QHead p) ->
--       do { x <- fresh "x"
--          ; u' <- flatten' ( CoCase [(rest,  u)
--                                            ,(QHead, App (CoCase coalts) (Var x))
--                                            ]
--                                   )
--          ; return (CoCase [(FQPat (FPVar x), u')
--                           ,(FQHead,cocase')]) }
--     x -> error $ "todo{flatten'}" <+> show x

-- -- R-Empty is id
-- flatten' (CoCase []) = return (CoCase [])


--------------------------------------------------------------------------------
--                              Flat Terms                                    --
--------------------------------------------------------------------------------
{- FlatTerms where added because in addition to having only flat (co)patterns,
they also have (co)case statements that contain defaults.

FlatTerms are a subset of Terms. -}
data FlatTerm where
  FLet :: Variable -> FlatTerm -> FlatTerm -> FlatTerm

  -- ^ Number primitives
  FLit :: Int -> FlatTerm
  FAdd :: FlatTerm -> FlatTerm -> FlatTerm

  FVar :: Variable -> FlatTerm
  FFix :: Variable -> FlatTerm -> FlatTerm
  FApp :: FlatTerm -> FlatTerm -> FlatTerm

  FCons :: Variable -> FlatTerm

  FCase :: FlatTerm               -- ^ Interrogated term
        -> (FlatPattern,FlatTerm) -- ^ Alternative
        -> FlatTerm               -- ^ Default case
        -> FlatTerm

  FDest :: Variable -> FlatTerm

  FCoCase :: (FlatCopattern,FlatTerm) -- ^ Coalternative
          -> FlatTerm                 -- ^ Default case
          -> FlatTerm

  FFail :: FlatTerm
  deriving (Eq,Show)

instance Pretty FlatTerm where
  ppInd _ (FLit i)         = show i
  ppInd i (FAdd a b)       = (parens . ppInd i $ a)
                         <+> "+"
                         <+> (parens . ppInd i $ b)
  ppInd _ (FVar s)         = s
  ppInd i (FFix s t)       = "fix" <+> s <+> "in" <-> indent i (ppInd (i+1) t)
  ppInd i (FLet s a b)     = "let" <+> s <+> "=" <+> ppInd (i+1) a
                         <-> indent i ("in" <+> ppInd (i+1) b)
  ppInd i (FApp a b)       = (parens . ppInd i $ a) <+> (parens . ppInd i $ b)
  ppInd _ (FCons k)        = k
  ppInd i (FCase t (p,u) d) = ("case" <+> ppInd i t)
                          <-> (indent (i+1) "{" <+> pp p <+> "->"
                               <+> (ppInd (i+2) u))
                          <-> (indent (i+1) "|" <+> "_ ->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd _ (FDest h)        = h
  ppInd i (FCoCase (q,u) d) = "cocase"
                          <-> (indent (i+1) "{" <+> pp q <+> "->"
                               <+> (ppInd (i+2) u))
                          <-> (indent (i+1) "," <+> "# ->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd _ FFail = "cocase {}"

data FlatPattern where
  FlatPatVar  :: Variable -> FlatPattern
  FlatPatCons :: Variable -> [Variable] -> FlatPattern
  deriving (Eq,Show)

instance Pretty FlatPattern where
  pp (FlatPatVar s)     = s
  pp (FlatPatCons k vs) = smconcat (k:vs)

data FlatCopattern where
  FlatCopDest :: Variable -> FlatCopattern
  FlatCopPat  :: FlatPattern -> FlatCopattern
  deriving (Eq,Show)

instance Pretty FlatCopattern where
  pp (FlatCopDest h)             = h <+> "#"
  pp (FlatCopPat (FlatPatVar v)) = "#" <+> v
  pp (FlatCopPat k)              = "#" <+> (parens . pp $ k)

--------------------------------------------------------------------------------
--                              Evaluation                                    --
--------------------------------------------------------------------------------
{- Evaluation is done over the more complex, recursive patterns and copatterns
-}
type Env = [(Variable,Term)]

{- An evaluation context for CoPatterns to match on -}
data ObsCtx where
  ObsHead :: ObsCtx
  ObsApp  :: ObsCtx -> Term -> ObsCtx
  ObsDest :: Variable -> ObsCtx -> ObsCtx
  deriving (Show,Eq)

{- The machine returns results which can be of positive or negative types. We
   call this result instead of value (as is the common approach) because of the
   polarity of values. -}
data Result where
  RInt       :: Int -> Result
  RConsApp   :: Variable -> [Term] -> Result
  RDest      :: Variable -> Result
  RCoCase    :: [(CoPattern,Term)] -> Result
  RMatchFail :: Result
  deriving (Eq,Show)

data Machine
  = Machine { run :: (Term, ObsCtx, Env) -> (Result, ObsCtx, Env) }

evalEmpty :: Term -> Result
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
  :: Term
  -> [(Pattern,Term)]
  -> Maybe (Term,[(Variable,Term)])
matchAlts _ []           = Nothing
matchAlts r ((p,u):alts) =
  case matchPattern r p of
    Just subs -> Just (u,subs)
    Nothing   -> matchAlts r alts

{- Takes a term and a pattern and returns a set of substitutions if it succeeds.
   Note that the set of substitutions can be empty. This is pretty standard. -}
matchPattern
  :: Term
  -> Pattern
  -> Maybe [(Variable,Term)]
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
  -> [(CoPattern,Term)]
  -> Maybe (Term,ObsCtx,[(Variable,Term)])
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
  -> Maybe (ObsCtx,[(Variable,Term)])

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
