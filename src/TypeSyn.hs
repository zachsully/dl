{-# LANGUAGE GADTs, DataKinds, KindSignatures, RankNTypes #-}
module TypeSyn where

import KindSyn
import VariableSyn
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

instance Pretty NegativeTyCons where
  pp tc = "codata" <+> negTyName tc

negTyArity :: NegativeTyCons -> Int
negTyArity = length . negTyFVars

data Projection
  = Proj
  { projName :: Variable
  , projDom  :: Type
  , projCod  :: Type }

data PositiveTyCons
  = PosTyCons
  { posTyName  :: TyVariable
  , posTyFVars :: [TyVariable]
  , injections :: [Injection]  }

instance Pretty PositiveTyCons where
  pp tc = "data" <+> posTyName tc

posTyArity :: PositiveTyCons -> Int
posTyArity = length . posTyFVars

data Injection
  = Inj
  { injName :: Variable
  , injCod  :: Type }
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}
