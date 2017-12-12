{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes #-}
module TypeSyn where

import Data.Set hiding (foldl)

import VariableSyn
import Pretty
import Utils

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
  pp (TyApp a b) = pp a <+> pp b

instance FV Type where
  fvs TyInt = empty
  fvs (TyArr a b) = fvs a `union` fvs b
  fvs (TyVar v) = singleton v
  fvs (TyCons _) = empty
  fvs (TyApp a b) = fvs a `union` fvs b

funArity :: Type -> Int
funArity (TyArr _ b) = 1 + funArity b
funArity _ = 0

codomain :: Type -> Type
codomain (TyArr _ b) = codomain b
codomain x = x


collectTyArgs :: Type -> Maybe (Variable,[Type])
collectTyArgs (TyApp e t) = collectTyArgs e >>= \(k,ts) -> return (k,t:ts)
collectTyArgs (TyCons k)  = return (k,[])
collectTyArgs _           = Nothing

distributeTyArgs :: (Variable,[Type]) -> Type
distributeTyArgs (k,ts) = foldl TyApp (TyCons k) ts

{- Intoduction of positive and negative types are done with NegativeTyCons and
   PositiveTyCons. These two are very similar. The notable difference is in
   projections and injections, where every projection must have domain and a
   codomain, injections may not take arguments. -}
data NegativeTyCons
  = NegTyCons
  { negTyName   :: Variable
  , negTyFVars  :: [Variable]
  , projections :: [Projection] }

instance Pretty NegativeTyCons where
  pp tc = "codata" <+> pp (negTyName tc)

negTyArity :: NegativeTyCons -> Int
negTyArity = length . negTyFVars

data Projection
  = Proj
  { projName :: Variable
  , projType  :: Type }

data PositiveTyCons
  = PosTyCons
  { posTyName  :: Variable
  , posTyFVars :: [Variable]
  , injections :: [Injection]  }

instance Pretty PositiveTyCons where
  pp tc = "data" <+> pp (posTyName tc)

posTyArity :: PositiveTyCons -> Int
posTyArity = length . posTyFVars

data Injection
  = Inj
  { injName :: Variable
  , injType  :: Type }
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}
