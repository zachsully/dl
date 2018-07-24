{-# LANGUAGE DataKinds,
             GADTs,
             KindSignatures,
             RankNTypes,
             UnicodeSyntax #-}
module DL.Syntax.Type where

import Data.Set hiding (foldl)

import DL.Syntax.Variable
import DL.Pretty
import DL.Utils

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

data Type :: * where
  TyInt  :: Type
  TyArr  :: Type -> Type -> Type
  TyVar  :: Variable -> Type
  TyCons :: Variable -> Type
  TyApp  :: Type -> Type -> Type
  deriving (Eq,Show)

instance Pretty Type where
  pp TyInt = "Int"
  pp (TyArr a b) = pp a <+> "→" <+> pp b
  pp (TyVar v) = unVariable v
  pp (TyCons k) = unVariable k
  pp (TyApp a b) = pp a <+> (parens . pp $ b)

instance FV Type where
  fvs TyInt = empty
  fvs (TyArr a b) = fvs a `union` fvs b
  fvs (TyVar v) = singleton v
  fvs (TyCons _) = empty
  fvs (TyApp a b) = fvs a `union` fvs b

arity :: Type -> Int
arity (TyArr _ b) = 1 + arity b
arity _ = 0

domain :: Type → Maybe Type
domain (TyArr a _) = Just a
domain _ = Nothing

codomain :: Type → Maybe Type
codomain (TyArr _ b) = Just (codomain' b)
  where codomain' (TyArr _ y) = codomain' y
        codomain' x = x
codomain _ = Nothing

collectTyArgs :: Type -> Maybe (Variable,[Type])
collectTyArgs (TyApp e t) = collectTyArgs e >>= \(k,ts) -> return (k,t:ts)
collectTyArgs (TyCons k)  = return (k,[])
collectTyArgs _           = Nothing

distributeTyArgs :: (Variable,[Type]) -> Type
distributeTyArgs (k,ts) = foldl TyApp (TyCons k) ts
