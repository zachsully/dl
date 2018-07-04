module Machine where

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

