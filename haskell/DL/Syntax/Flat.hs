{-# LANGUAGE GADTs, KindSignatures #-}
module DL.Syntax.Flat where

import Control.Monad.State
import Data.Foldable (foldrM)
import Data.Monoid ((<>))
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Variable
import DL.Pretty

--------------------------------------------------------------------------------
--                              Flat Terms                                    --
--------------------------------------------------------------------------------
{- FlatTerms where added because in addition to having only flat (co)patterns,
they also have (co)case statements that contain defaults.

FlatTerms are a subset of Terms. -}
data FlatTerm :: * where
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
        -> (Variable,FlatTerm)    -- ^ Default case
        -> FlatTerm

  FDest :: Variable -> FlatTerm

  FCocase :: (FlatCopattern,FlatTerm) -- ^ Coalternative
          -> FlatTerm                 -- ^ Default case
          -> FlatTerm

  FFail :: FlatTerm
  deriving (Eq,Show)

instance Pretty FlatTerm where
  ppInd _ (FLit i)         = show i
  ppInd i (FAdd a b)       = (parens . ppInd i $ a)
                         <+> "+"
                         <+> (parens . ppInd i $ b)
  ppInd _ (FVar s)         = pp s
  ppInd i (FFix s t)       = "fix" <+> pp s <+> "in" <-> indent i (ppInd (i+1) t)
  ppInd i (FLet s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                         <-> indent i ("in" <+> ppInd (i+1) b)
  ppInd i (FApp a b)       = (parens . ppInd i $ a) <+> (parens . ppInd i $ b)
  ppInd _ (FCons k)        = pp k
  ppInd i (FCase t (p,u) (y,d)) = ("case" <+> ppInd i t)
                          <-> (indent (i+1) "{" <+> pp p <+> "->"
                               <+> (ppInd (i+2) u))
                          <-> (indent (i+1) "|" <+> pp y <+> "->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd _ (FDest h)        = pp h
  ppInd i (FCocase (q,u) d) = "cocase"
                          <-> (indent (i+1) "{" <+> pp q <+> "->"
                               <+> (ppInd (i+2) u))
                          <-> (indent (i+1) "," <+> "# ->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd _ FFail = "(cocase {})"

data FlatPattern where
  FlatPatVar  :: Variable -> FlatPattern
  FlatPatCons :: Variable -> [Variable] -> FlatPattern
  deriving (Eq,Show)

instance Pretty FlatPattern where
  pp (FlatPatVar s)     = pp s
  pp (FlatPatCons k vs) = smconcat (pp k:fmap pp vs)

data FlatCopattern where
  FlatCopDest :: Variable -> FlatCopattern
  FlatCopPat  :: FlatPattern -> FlatCopattern
  deriving (Eq,Show)

instance Pretty FlatCopattern where
  pp (FlatCopDest h)             = pp h <+> "#"
  pp (FlatCopPat (FlatPatVar v)) = "#" <+> pp v
  pp (FlatCopPat k)              = "#" <+> (parens . pp $ k)


--------------------------------------------------------------------------------
--                     Flattening Transformation                              --
--------------------------------------------------------------------------------

flattenPgm :: Program Term -> Program FlatTerm
flattenPgm pgm = Pgm (pgmDecls pgm) (flatten . pgmTerm $ pgm)


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
  do { t' <- flatten' t
     ; y <- fresh (Variable "y")
     ; out <- cata y alts
     ; case out of
         Nothing -> return FFail
         Just (alt',def) -> return (FCase t' alt' def)
     }
  where cata :: Variable
             -> [(Pattern, Term)]
             -> State Int (Maybe ((FlatPattern,FlatTerm),(Variable, FlatTerm)))
        cata y [] = return Nothing
        cata y ((PVar v,u):_) =
          do { u' <- flatten' u
             ; return . Just $ ((FlatPatVar v,u'),(y,FFail))
             }
        cata y ((PCons c ps,u):rest) =
          do { y' <- fresh (Variable "y")
             ; u' <- flatten' u
             ; out' <- cata y' rest
             ; case out' of
                 Nothing -> return . Just $ ((FlatPatCons c [],u'),(y, FFail))
                 Just (alt'',def') ->
                   return . Just $ ((FlatPatCons c [],u')
                                   ,(y,FCase (FVar y) alt'' def'))
             }

flatten' (Coalts ((QHead,u):_)) = flatten' u    -- R-QHead

flatten' (Coalts ((QPat QHead (PVar v),u):_)) = -- R-QPVar
  do { u' <- flatten' u
     ; return (FCocase (FlatCopPat (FlatPatVar v), u') FFail) }

flatten' (Coalts ((QPat QHead p,u):coalts)) =   -- R-QPat
  do { v <- fresh (Variable "p")
     ; y <- fresh (Variable "y")
     ; let t = Case (Var v) [(p,u),(PVar y,Coalts coalts)]
     ; t' <- flatten' t
     ; return (FCocase (FlatCopPat (FlatPatVar v), t') FFail)
     }

flatten' (Coalts ((QDest h QHead,u):coalts)) =  -- R-QDest
  do { u' <- flatten' u
     ; coalts' <- flatten' (Coalts coalts)
     ; return (FCocase (FlatCopDest h,u') coalts')
     }

{- Here we add in a case for what to do when there is only one copattern
 left. Because of our call-by-value translation 'cocase {}' cannot be
 applied. We need to know when this is produced and handle it in an adhoc way.
-}
flatten' (Coalts ((q,u):[])) =
  flatten' u >>= \u' ->
  case unplugCopattern q of
    (Just rest, QPat QHead p) ->
      do { let u' = Coalts [(rest,  u)]
         ; u'' <- flatten' u'
         ; flatten' (Coalts [(QPat QHead p, u')])
         }
    (Just rest, QDest h QHead) ->
      do { u' <- flatten' ( Coalts [(rest,  u) ] )
         ; return (FCocase (FlatCopDest h, u') FFail) }
    x -> error $ "TODO flatten'{" <> show x <> "}"


flatten' (Coalts ((q,u):coalts)) =              -- R-Rec
  flatten' (Coalts coalts) >>= \cocase' ->
  flatten' u >>= \u' ->
  case unplugCopattern q of
    (Just rest, QPat QHead p) ->
      do { v  <- fresh (Variable "coalt")
         ; let u' = Coalts [(rest,  u),(QHead, App (Var v) (invertPattern p))]
         ; u'' <- flatten' u'
         ; flatten' (Let v (Coalts coalts) (Coalts [(QPat QHead p, u'),(QHead,Var v)]))
         }
    (Just rest, QDest h QHead) ->
      do { v  <- fresh (Variable "coalt")
         ; u' <- flatten' ( Coalts [(rest,  u)
                                   ,(QHead, App (Dest h) (Var v))
                                   ]
                           )
         ; return (FLet v cocase' (FCocase (FlatCopDest h, u') (FVar v))) }
    x -> error $ "TODO flatten'{" <> show x <> "}"

flatten' (Coalts []) = return FFail -- R-Empty

--------------------
-- Unsubstituting --
--------------------

fromFlatCop :: FlatCopattern -> CoPattern
fromFlatCop (FlatCopDest v) = QDest v QHead
fromFlatCop (FlatCopPat p) = QPat QHead (fromFlatPat p)

fromFlatPat :: FlatPattern -> Pattern
fromFlatPat (FlatPatVar v) = PVar v
fromFlatPat (FlatPatCons c vs) = PCons c (fmap PVar vs)

substCop :: FlatCopattern -> CoPattern -> CoPattern
substCop fq QHead = fromFlatCop fq
substCop fq (QDest h q) = QDest h (substCop fq q)
substCop fq (QPat q p) = QPat (substCop fq q) p

unsubstCop :: CoPattern -> Maybe (CoPattern,CoPattern)
unsubstCop QHead       = Nothing
unsubstCop (QDest h q) = case unsubstCop q of
                           Nothing -> Just (QDest h QHead, QHead)
                           Just (s,q') -> Just (s, QDest h q')
unsubstCop (QPat q p)  = case unsubstCop q of
                            Nothing -> Just (QPat QHead p, QHead)
                            Just (s,q') -> Just (s, QPat q' p)
