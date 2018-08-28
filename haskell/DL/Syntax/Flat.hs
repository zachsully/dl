{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

{- |
Module      : DL.Syntax.Flat
Description : Gives the flat core language for the compiler. Provides a
              transformation from the source to core language
-}
module DL.Syntax.Flat
  ( -- * Core flat language
    FlatTerm (..)
  , FlatPattern (..)
  , FlatObsCtx (..)

    -- * Transformation to core language
  , flattenPgm
  , flatten
  ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Monoid ((<>))
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Variable
import DL.Pretty

--------------------------------------------------------------------------------
--                              Flat Terms                                    --
--------------------------------------------------------------------------------
-- | FlatTerms where added because in addition to having only flat (co)patterns,
-- they also have (co)case statements that contain defaults. FlatTerms are a
-- subset of Terms.
data FlatTerm :: * where
  FLet       :: Variable -> FlatTerm -> FlatTerm -> FlatTerm
  FVar       :: Variable -> FlatTerm
  FFix       :: Variable -> FlatTerm -> FlatTerm

  FLit       :: Int -> FlatTerm
  FAdd       :: FlatTerm -> FlatTerm -> FlatTerm

  FConsApp   :: Variable -> [FlatTerm] -> FlatTerm
  -- | Interrogated term -> Alternative -> Default case
  FCase      :: FlatTerm
             -> (FlatPattern,FlatTerm)
             -> (Variable,FlatTerm)
             -> FlatTerm
  FCaseEmpty :: FlatTerm -> FlatTerm

  FCocase    :: FlatObsCtx -> FlatTerm -> FlatTerm
  -- | Copattern match on applicative
  FFun       :: Variable -> FlatTerm -> FlatTerm
  -- | Destructor coalternative -> default case
  FCoalt     :: (Variable,FlatTerm)
             -> FlatTerm
             -> FlatTerm
  -- | Like a shift operation, the variable bould is a covariable
  FShift     :: Variable -> FlatTerm -> FlatTerm
  -- | A failure copattern match
  FEmpty     :: FlatTerm
  deriving (Eq,Show)

instance Pretty FlatTerm where
  ppInd _ (FLit i)         = show i
  ppInd i (FAdd a b)       = (parens' a . ppInd i $ a)
                         <+> "+"
                         <+> (parens' b . ppInd i $ b)
  ppInd _ (FVar s)         = pp s
  ppInd i (FFix s t)       = "fix" <+> pp s <+> "in"
                           <-> indent (i+5) (ppInd (i+5) t)
  ppInd i (FLet s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                            <-> indent i ("in" <+> ppInd (i+3) b)
  ppInd _ (FConsApp k [])  = pp k
  ppInd i (FConsApp k vs@(_:_))  = pp k <+> smconcat . fmap (ppInd (i+1)) $ vs
  ppInd i (FCase t (p,u) (y,d)) = ("case" <+> parens' t (ppInd (i+6) t))
                          <-> (indent (i+2) "{" <+> pp p <+> "->"
                               <+> (ppInd (i+4) u))
                          <-> (indent (i+2) "|" <+> pp y <+> "->"
                               <+> (ppInd (i+4) d))
                          <-> (indent (i+2) "}")
  ppInd i (FCaseEmpty t) = "case" <+> ppInd (i+5) t <+> "{}"
  ppInd i (FCocase c t)    = "cocase" <-> indent (i+2) (ppInd (i+2) c)
                                      <-> indent (i+2) (parens' t . ppInd (i+2) $ t)

  ppInd i (FFun v t)       =  "{ #" <+> ppInd i v <+> "->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd i (FCoalt (h,u) d) = "{" <+> pp h <+> "# ->"
                               <-> indent (i+3) (ppInd (i+3) u)
                          <-> (indent (i+3) "," <+> "_ ->"
                               <+> (ppInd (i+3) d))
                          <-> (indent (i+3) "}")
  ppInd i (FShift v t)    =  "{" <+> ppInd i v <+> "# ->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd _ FEmpty           = "{}"

-- | Do we not need parens when pretty printing?
atomic :: FlatTerm -> Bool
atomic (FLet _ _ _) = False
atomic (FVar _) = True
atomic (FFix _ _) = False
atomic (FLit _) = True
atomic (FAdd _ _) = False
atomic (FConsApp _ []) = True
atomic (FConsApp _ (_:_)) = False
atomic (FCase _ _ _) = False
atomic (FCaseEmpty _) = False
atomic (FCocase _ _) = False
atomic (FFun _ _) = True
atomic (FCoalt _ _) = True
atomic (FShift _ _) = True
atomic FEmpty = True

-- | Print parens if not atomic
parens' :: FlatTerm -> String -> String
parens' t s =
  case atomic t of
    True -> s
    False -> parens s

data FlatPattern where
  FlatPatVar  :: Variable -> FlatPattern
  FlatPatCons :: Variable -> [Variable] -> FlatPattern
  deriving (Eq,Show)

instance Pretty FlatPattern where
  pp (FlatPatVar s)     = pp s
  pp (FlatPatCons k vs) = smconcat (pp k:fmap pp vs)

data FlatObsCtx :: * where
  FlatObsFun  :: FlatTerm -> FlatObsCtx
  FlatObsDest :: Variable -> FlatObsCtx
  FlatObsCut  :: Variable -> FlatObsCtx
  deriving (Show, Eq)

instance Pretty FlatObsCtx where
  ppInd _ (FlatObsDest h) = brackets (pp h <+> "#")
  ppInd i (FlatObsFun t)  = "[#" <+> (parens' t . ppInd (i+3) $ t) <> "]"
  ppInd _ (FlatObsCut v)  = brackets (pp v <+> "#")

data FlatCopattern
  = FlatQHead
  | FlatQDest Variable
  | FlatQPat FlatPattern

instance Pretty FlatCopattern where
  ppInd _ FlatQHead = "#"
  ppInd _ (FlatQDest h) = pp h <+> "#"
  ppInd _ (FlatQPat p) = "#" <+> pp p

--------------------------------------------------------------------------------
--                       Unflattening Transformation                          --
--------------------------------------------------------------------------------
-- | unflatten is required for flattening. It is not the case that
-- prop> forall t. unflatten (flatten t) = t.
-- This is because of the introduction of default alternatives and
-- coalternatives
unflatten :: FlatTerm -> Term
unflatten (FLet v e t) = Let v (unflatten e) (unflatten t)
unflatten (FVar v) = Var v
unflatten (FFix v t) = Fix v (unflatten t)
unflatten (FLit i) = Lit i
unflatten (FAdd a b) = Add (unflatten a) (unflatten b)
unflatten (FConsApp k ts) = distributeArgs (k,fmap unflatten ts)
unflatten (FCase t (p,u) (v,d))
  = Case (unflatten t)
         [(case p of
             FlatPatVar w -> PVar w
             FlatPatCons k vs -> PCons k (fmap PVar vs)
          ,unflatten u)
         ,(PVar v,unflatten d)]
unflatten (FCaseEmpty t) = Case (unflatten t) []
unflatten (FCocase o t) = Cocase (unflattenObsCtx o) (unflatten t)
unflatten (FFun v t) = Coalts [(QPat QHead (PVar v),unflatten t)]
unflatten (FCoalt (h,t) d) = Coalts [(QDest h QHead,unflatten t)
                                    ,(QWild, unflatten d)]
unflatten (FShift a t) = Coalts [(QVar a QHead, unflatten t)]
unflatten FEmpty = Coalts []

unflattenObsCtx :: FlatObsCtx -> ObsCtx
unflattenObsCtx (FlatObsFun t)  = ObsFun ObsHead (unflatten t)
unflattenObsCtx (FlatObsDest h) = ObsDest h ObsHead
unflattenObsCtx (FlatObsCut v) = ObsCut v ObsHead


--------------------------------------------------------------------------------
--                        Flattening Transformation                           --
--------------------------------------------------------------------------------
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

-- | We define a newtype for the FlatM for better error messages
newtype FlatM a = FlatM { unFlatM :: ReaderT [(Variable,Int)] (State Int) a }

instance Functor FlatM where
  fmap f (FlatM m) = FlatM (fmap f m)

instance Applicative FlatM where
  pure = return
  (<*>) = ap

instance Monad FlatM where
  return x = FlatM (return x)
  (FlatM m) >>= g = FlatM (m >>= (unFlatM . g))

instance MonadReader [(Variable,Int)] FlatM where
  ask = FlatM ask
  local r (FlatM m) = FlatM (local r m)

instance MonadState Int FlatM where
  get = FlatM get
  put x = FlatM (put x)

fresh :: Variable -> FlatM Variable
fresh v = do { n <- get
             ; put (succ n)
             ; return . Variable $ (unVariable v <> show n) }

-------------------------------------------
-- | Entry point for flattening a program
flattenPgm :: Program Term -> Program FlatTerm
flattenPgm p = Pgm (pgmDecls p)
                   (flatten (pgmConsDestArity p) . pgmTerm $ p)

-- | Flatten a term given a list of Cons/Dest arities
flatten :: [(Variable,Int)] -> Term -> FlatTerm
flatten w t = fst (runState (runReaderT (unFlatM (flatten' t)) w) 0)

-- | flatten' is the heart of the flattening pass. The interesting cases are
-- Cons and Dests (which are eta expanded) and Case, Cocase, and Coalternatives.
flatten' :: Term -> FlatM FlatTerm
flatten' (Ann t _)     = flatten' t
flatten' (Prompt t)    = flatten' t
flatten' (App a b)     = FCocase <$> (FlatObsFun <$> flatten' b) <*> flatten' a
flatten' (Let v a b)   = FLet v <$> flatten' a <*> flatten' b
flatten' (Lit i)       = return (FLit i)
flatten' (Add a b)     = FAdd <$> flatten' a <*> flatten' b
flatten' (Var v)       = return (FVar v)
flatten' (Fix v t)     = FFix v <$> flatten' t

-- ^ Eta expand all constructors, e.g. K ==> { # x y z -> K x y z } where K has
--  arity 3. This is done so that we can eliminate the overloaded application
--  nodes. The arity for constructors is stored in the map contained in the
--  FlatM monad.
flatten' (Cons k)      =
  ask >>= \w ->
  case lookup k w of
    Just i  ->
      do { vs <- replicateM i (fresh (Variable "k"))
         ; return (foldr (\v t -> FFun v t) (FConsApp k (fmap FVar vs)) vs) }
    Nothing -> error "flatten' should not happen"

flatten' (Case t alts) = flattenAlts alts =<< flatten' t

-- ^ Eta expand all destructors, e.g.  H ==> { # x -> cocase (H #) x }. This is
--   done so that we can eliminate the overloaded application nodes. Arity for
--   destructors is stored in map `w`, but will always be 1.
flatten' (Dest h) =
  do { x <- fresh (Variable "dx")
     ; return (FFun x (FCocase (FlatObsDest h) (FVar x))) }

flatten' (Cocase c t) = go (unplugObsCtx c) =<< flatten' t
  where go (Nothing, ObsHead) e = return e
        go (Nothing, ObsFun ObsHead u) e =
          do { u' <- flatten' u
             ; return (FCocase (FlatObsFun u') e) }
        go (Nothing, ObsDest h ObsHead) e =
          return (FCocase (FlatObsDest h) e)
        go (Nothing, ObsCut v ObsHead) e =
          return (FCocase (FlatObsCut v) e)
        go (Just c', ObsFun _ u) e =
          do { e' <- go (unplugObsCtx c') e
             ; u' <- flatten' u
             ; return (FCocase (FlatObsFun u') e') }
        go (Just c', ObsDest h _) e =
          do { e' <- go (unplugObsCtx c') e
             ; return (FCocase (FlatObsDest h) e') }
        go (Just c', ObsCut v _) e =
          do { e' <- go (unplugObsCtx c') e
             ; return (FCocase (FlatObsCut v) e') }
        go x _ = error $ "this should not happen. Flatten ObsCtx" <+> show x

flatten' (Coalts coalts) = flattenCoalts coalts

{-
The bits that flatten alternatives and coalternatives are the trickiest parts of
this compiler. The two have to work similarly because we nest patterns inside of
copatterns.
-}

-- | flattenAlts takes a list of alternatives and the interrogated term and
-- builds a flattened expression
flattenAlts :: [(Pattern,Term)] -> FlatTerm -> FlatM FlatTerm
flattenAlts [] e             = return (FCaseEmpty e)
flattenAlts ((PVar v,u):_) e =
  do { y <- fresh (Variable "y")
     ; u' <- flatten' u
     ; return (FCase e (FlatPatVar v,u') (y,FEmpty)) }
flattenAlts ((PWild,u):_)  e =
  do { v <- fresh (Variable "wild")
     ; y <- fresh (Variable "y")
     ; u' <- flatten' u
     ; return (FCase e (FlatPatVar v,u') (y,FEmpty)) }
flattenAlts (alt:alts) e =
  do { y <- fresh (Variable "y")
     ; def <- flattenAlts alts (FVar y)
     ; alt' <- flattenAlt alt
     ; return (FCase e alt' (y,def)) }

-- | flattenAlt is responsible for flattening its pattern and producing a
-- flattened version of its term. Flattening the pattern can add new case
-- expressions to the term.
flattenAlt :: (Pattern,Term) -> FlatM (FlatPattern,FlatTerm)
flattenAlt (PVar v,u) =
  do { u' <- flatten' u
     ; return (FlatPatVar v,u') }
flattenAlt (PWild, u) =
  do { v <- fresh (Variable "wild")
     ; u' <- flatten' u
     ; return (FlatPatVar v, u') }
flattenAlt (PCons k ps, u) =
  do { u' <- flatten' u
     ; (vs,rhs) <- foldM (\(vs,rhs) p -> flattenPattern  p vs rhs) ([],u') ps
     ; return (FlatPatCons k vs,rhs) }

flattenPattern
  :: Pattern
  -> [Variable]
  -> FlatTerm
  -> FlatM ([Variable],FlatTerm)
flattenPattern PWild vs rhs =
  do { v <- fresh (Variable "wild")
     ; return (v:vs, rhs) }
flattenPattern (PVar v) vs rhs = return (v:vs,rhs)
flattenPattern p@(PCons _ _) vs rhs =
  do { v <- fresh (Variable "p")
     ; alt <- flattenAlt (p,unflatten rhs)
     ; failp <- fresh (Variable "fail")
     ; return (v:vs,FCase (FVar v) alt (failp,FEmpty)) }

-- | flattenCoalts handles lists of coalternatives
flattenCoalts :: [(CoPattern,Term)] -> FlatM FlatTerm
flattenCoalts [] = return FEmpty
flattenCoalts (coalt:coalts) =
  do { def <- flattenCoalts coalts
     ; flattenCoalt coalt def }

-- | flattenCoalt takes a coalternative and the defaults branch and builds the
-- final output
flattenCoalt :: (CoPattern,Term) -> FlatTerm -> FlatM FlatTerm
flattenCoalt (QHead,u) _ = flatten' u
flattenCoalt (QWild,u) _ = flatten' u
flattenCoalt (QVar v QHead,u) _ =
  do { u' <- flatten' u
     ; return (FShift v u') }
flattenCoalt (QDest h QHead,u) def =
  do { u' <- flatten' u
     ; return (FCoalt (h,u') def) }
flattenCoalt (QPat QHead (PVar v),u) _ = FFun v <$> flatten' u
flattenCoalt (QPat QHead p,u) def =
  do { x <- fresh (Variable "x")
     ; y <- fresh (Variable "y")
     ; rhs <- flatten' (Case (Var x) [(p,u)
                                     ,(PVar y, App (unflatten def) (Var x))])
     ; return (FFun x rhs)
     }
-- ^ Here we add in a case for what to do when there is only one copattern
-- left. Because of our call-by-value translation '{}' cannot be applied. We
-- need to know when this is produced and handle it in an adhoc way.
flattenCoalt (q,u) FEmpty =
  case unplugCopattern q of
    (Just q', QPat QHead p) ->
      flatten' (Coalts [(QPat QHead p, Coalts [(q', u)])])
    (Just q', QDest h QHead) ->
      do { u' <- flatten' (Coalts [(q', u)])
         ; return (FCoalt (h, u') FEmpty) }
    x -> error $ "flattenCoalt:" <+> show x
flattenCoalt (q,u) def =
 case unplugCopattern q of
   (Just rest, QPat QHead p) ->
     do { v  <- fresh (Variable "coalt")
        ; let u' = Coalts [(rest,  u)
                           ,(QHead, App (Var v) (invertPattern p))]
        ; flatten' (Let v (Coalts [(QHead,unflatten def)])
                    (Coalts [(QPat QHead p, u'),(QHead,Var v)]))
        }
   (Just q', QDest h QHead) ->
     do { v  <- fresh (Variable "coalt")
        ; u' <- flatten' (Coalts [(q',u),(QHead, App (Dest h) (Var v))])
        ; return (FLet v def
                  (FCoalt (h, u') (FVar v))) }
   x -> error $ "flattenCoalt:" <+> show x
