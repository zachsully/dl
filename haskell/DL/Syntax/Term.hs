{-# LANGUAGE GADTs, DataKinds, RankNTypes, KindSignatures #-}
module DL.Syntax.Term where

import Data.Monoid ((<>))
import Data.Set ((\\),singleton,empty,union,unions,Set)

import DL.Syntax.Type
import DL.Syntax.Variable
import DL.Pretty
import DL.Utils

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------
{- Terms are parameterized over the type of pattern and copattern. This is
important because we only translate flat (co)patterns. -}
data Term where
  Let :: Variable -> Term -> Term -> Term
  Ann :: Term -> Type -> Term

  -- ^ Number primitives
  Lit :: Int -> Term
  Add :: Term -> Term -> Term

  Var   :: Variable -> Term
  Fix   :: Variable -> Term -> Term
  App   :: Term -> Term -> Term

  Cons   :: Variable -> Term
  Case   :: Term -> [(Pattern,Term)] -> Term

  Dest   :: Variable -> Term
  Coalts :: [(CoPattern,Term)] -> Term
  Cocase :: ObsCtx -> Term -> Term

  Prompt :: Term -> Term -- sets a point to delimit continuations
  deriving (Eq,Show)

instance Pretty Term where
  ppInd _ (Lit i)         = show i
  ppInd i (Ann t ty)      = parens (ppInd i t <+> ":" <+> ppInd (i+1) ty)
  ppInd i (Add a b)       = (parens . ppInd i $ a)
                        <+> "+"
                        <+> (parens . ppInd i $ b)
  ppInd _ (Var s)         = pp s
  ppInd i (Fix s t)       = "fix" <+> pp s <+> "in" <-> indent i (ppInd (i+1) t)
  ppInd i (Let s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                        <-> indent i ("in" <+> ppInd (i+1) b)
  ppInd i (App a b)       = (parens . ppInd i $ a) <+> (parens . ppInd i $ b)
  ppInd _ (Cons k)        = pp k
  ppInd i (Case t alts)   = "case"
                        <+> ppInd i t
                        <-> indent (i+1) "{"
                        <+> ( stringmconcat ("\n" <> (indent (i+1) "| "))
                            . fmap (\(p,u) -> pp p <+> "->" <+> ppInd (i+2) u)
                            $ alts)
                        <-> indent (i+1) "}"
  ppInd _ (Dest h)        = pp h
  ppInd i (Cocase c t)    = "cocase" <+> ppInd (i+1) c
                                     <-> indent (i+1) (ppInd (i+2) t)
  ppInd _ (Coalts [])     = "{}"
  ppInd i (Coalts coalts) = "{"
                        <+> ( stringmconcat ("\n" <> (indent (i+1) ", "))
                            . fmap (\(q,u) -> pp q <+> "->" <+> ppInd (i+2) u)
                            $ coalts)
                        <-> indent (i+1) "}"
  ppInd i (Prompt t)      = "#" <+> ppInd (i+1) t

instance FV Term where
  fvs (Let v a b) = fvs a `union` (fvs b \\ singleton v)
  fvs (Ann a _) = fvs a
  fvs (Lit _) = empty
  fvs (Add a b) = fvs a `union` fvs b
  fvs (Var v) = singleton v
  fvs (Fix v a) = fvs a \\ singleton v
  fvs (App a b) =  fvs a `union` fvs b
  fvs (Cons _) = empty
  fvs (Case a alts) =
    fvs a `union` (unions (fmap (\(p,u) -> fvs u \\ patBinds p) alts))
  fvs (Dest _) = empty
  fvs (Cocase obsctx t) = fvs obsctx `union` fvs t
  fvs (Coalts coalts) = unions . fmap (\(q,u) -> fvs u \\ copBinds q) $ coalts
  fvs (Prompt a) = fvs a

{-
`collectArgs` will recur down an application to find the constructor and its
arguments
-}
collectArgs :: Term -> Maybe (Variable,[Term])
collectArgs (App e t) = collectArgs e >>= \(k,ts) -> return (k,t:ts)
collectArgs (Cons k)  = return (k,[])
collectArgs _         = Nothing

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[Term]) -> Term
distributeArgs (k,ts) = foldl App (Cons k) ts

-------------------------
-- Observable Contexts --
-------------------------

data ObsCtx :: * where
  ObsHead :: ObsCtx
  ObsFun  :: ObsCtx -> Term -> ObsCtx
  ObsDest :: Variable -> ObsCtx -> ObsCtx
  deriving (Show, Eq)

instance Pretty ObsCtx where
  pp ObsHead       = "#"
  pp (ObsDest h c) = pp h <+> (brackets . pp $ c)
  pp (ObsFun c t)  = (brackets . pp $ c) <+> (parens . pp $ t)

instance FV ObsCtx where
  fvs ObsHead = empty
  fvs (ObsFun c t) = fvs c `union` fvs t
  fvs (ObsDest _ c) = fvs c

plugObsCtx :: ObsCtx -> ObsCtx -> ObsCtx
plugObsCtx ObsHead       c' = c'
plugObsCtx (ObsDest h c) c' = ObsDest h (plugObsCtx c c')
plugObsCtx (ObsFun c t)  c' = ObsFun (plugObsCtx c c') t

unplugObsCtx :: ObsCtx -> (Maybe ObsCtx,ObsCtx)
unplugObsCtx ObsHead             = (Nothing, ObsHead)
unplugObsCtx (ObsFun ObsHead t)  = (Nothing, ObsFun ObsHead t)
unplugObsCtx (ObsDest h ObsHead) = (Nothing, ObsDest h ObsHead)
unplugObsCtx (ObsFun c t)        =
  let (m,i) = unplugObsCtx c in
    case m of
      Nothing -> (Just (ObsFun ObsHead t), i)
      Just c' -> (Just (ObsFun c' t), i)
unplugObsCtx (ObsDest h c)       =
  let (m,i) = unplugObsCtx c in
    case m of
      Nothing -> (Just (ObsDest h ObsHead), i)
      Just c' -> (Just (ObsDest h c'), i)

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
  pp (PVar s)     = pp s
  pp (PCons k ps) = pp k <+> (smconcat . fmap (parens . pp) $ ps)

patBinds :: Pattern -> Set Variable
patBinds PWild = empty
patBinds (PVar v) = singleton v
patBinds (PCons _ ps) = unions (fmap patBinds ps)

invertPattern :: Pattern -> Term
invertPattern PWild = error "cannot invert wildcard"
invertPattern (PVar v) = Var v
invertPattern (PCons k ps) = distributeArgs (k,fmap invertPattern ps)

{- Copatterns -}
{- NOTE: we often use 'q' for a copattern variables -}
data CoPattern where
  QHead :: CoPattern                          -- ^ the copattern matching the context
  QDest :: Variable -> CoPattern -> CoPattern -- ^ a specific destructor
  QPat  :: CoPattern -> Pattern -> CoPattern  -- ^ a copattern applied ot a pattern
  QVar  :: Variable -> CoPattern -> CoPattern -- ^ a covariable to bind continuations
  deriving (Eq,Show)

instance Pretty CoPattern where
  pp QHead       = "#"
  pp (QDest h q) = pp h <+> (brackets . pp $ q)
  pp (QPat q p)  = (brackets . pp $ q) <+> (parens . pp $ p)
  pp (QVar v q)  = pp v <+> (brackets . pp $ q)

copBinds :: CoPattern -> Set Variable
copBinds QHead = empty
copBinds (QDest _ q) = copBinds q
copBinds (QPat q p) = patBinds p `union` copBinds q
copBinds (QVar v q) = singleton v `union` copBinds q

-- replace head with copattern in copattern
plugCopattern :: CoPattern -> CoPattern -> CoPattern
plugCopattern QHead       q' = q'
plugCopattern (QDest h q) q' = QDest h (plugCopattern q q')
plugCopattern (QPat q p)  q' = QPat (plugCopattern q q') p
plugCopattern (QVar v q)  q' = QVar v (plugCopattern q q')

{-
Used in the context filling rules R-RecPat and R-RedDest, Takes a copattern and
returns (an optional new copattern with the inner most matchable pattern pulled
out and replace by head) and the inner most copattern
-}

unplugCopattern :: CoPattern -> (Maybe CoPattern,CoPattern)
unplugCopattern QHead           = (Nothing, QHead)
unplugCopattern (QPat QHead p)  = (Nothing, QPat QHead p)
unplugCopattern (QDest h QHead) = (Nothing, QDest h QHead)
unplugCopattern (QVar _ QHead)  = (Nothing, error "unplugCopatter{QVar}")
unplugCopattern (QDest h q)     = let (m,i) = unplugCopattern q in
                                  case m of
                                    Nothing -> (Just (QDest h QHead), i)
                                    Just q' -> (Just (QDest h q'), i)
unplugCopattern (QPat q p)      = let (m,i) = unplugCopattern q in
                                  case m of
                                    Nothing -> (Just (QPat QHead p), i)
                                    Just q' -> (Just (QPat q' p), i)
unplugCopattern (QVar v q)      = let (m,i) = unplugCopattern q in
                                  case m of
                                    Nothing -> (Just (QVar v QHead), i)
                                    Just q' -> (Just (QVar v q'), i)

-----------------------------
-- Some smart constructors --
-----------------------------

lam :: Variable -> Term -> Term
lam v t = Coalts [(QPat QHead (PVar v), t)]
