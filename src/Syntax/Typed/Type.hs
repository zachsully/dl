{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes #-}
module Syntax.Typed.Type where

import Syntax.Typed.Kind
import Syntax.Variable
import Pretty

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

data Type :: Kind -> * where
  TyInt  :: Type 'KStar
  TyArr  :: Type 'KStar -> Type 'KStar -> Type 'KStar
  TyVar  :: Variable -> Type 'KStar
  TyCons :: Variable -> Type 'KStar
  TyApp  :: Type 'KStar -> Type 'KStar -> Type 'KStar

ppType :: forall k . Type k -> String
ppType TyInt = "Int"
ppType (TyArr a b) = ppType a <+> "->" <+> ppType b
ppType (TyVar v) = v
ppType (TyCons k) = k
ppType (TyApp a b) =  ppType a <+> ppType b

collectTyArgs :: forall k . Type k -> Maybe (Variable,[Type k])
collectTyArgs (TyApp e t) = collectTyArgs e >>= \(k,ts) -> return (k,t:ts)
collectTyArgs (TyCons k)  = return (k,[])
collectTyArgs _           = Nothing

distributeTyArgs :: forall k . (Variable,[Type KStar]) -> Type KStar
distributeTyArgs (k,ts) = foldl TyApp (TyCons k) ts


{- Intoduction of positive and negative types are done with NegativeTyCons and
   PositiveTyCons. These two are very similar. The notable difference is in
   projections and injections, where every projection must have domain and a
   codomain, injections may not take arguments. -}
data NegativeTyCons k
  = NegTyCons
  { negTyName   :: Variable
  , negTyFVars  :: [Variable]
  , projections :: [Projection k] }

instance Pretty (NegativeTyCons k) where
  pp tc = "codata" <+> negTyName tc

negTyArity :: forall k . NegativeTyCons k -> Int
negTyArity = length . negTyFVars

data Projection k
  = Proj
  { projName :: Variable
  , projDom  :: Type k
  , projCod  :: Type k }

data PositiveTyCons k
  = PosTyCons
  { posTyName  :: Variable
  , posTyFVars :: [Variable]
  , injections :: [Injection k]  }

instance Pretty (PositiveTyCons k) where
  pp tc = "data" <+> posTyName tc

posTyArity :: forall k . PositiveTyCons k -> Int
posTyArity = length . posTyFVars

data Injection k
  = Inj
  { injName :: Variable
  , injCod  :: Type k }
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}
