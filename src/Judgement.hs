module Judgement where

import DualSyn

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

typeOfProgram :: Program -> Type
typeOfProgram (Program decls term) = undefined

--------------------------------------------------------------------------------
--                                isType                                      --
--------------------------------------------------------------------------------
{- Checks whether a type is well formed -}

type Signature = [Decl]

isType :: Signature           -- ^ A set of type signatures
       -> [(TyVariable,Type)] -- ^ A context of bindings of type variables
       -> Type
       -> Bool
isType _ ctx TyInt            = True
isType s ctx (TyArr a b)      = isType s ctx a && isType s ctx b
isType s ctx (TyVar v)        = case lookup v ctx of
                                  Just t -> isType s ctx t
                                  Nothing -> False
isType s ctx (TyCons sym tys) = case lookupDecl sym s of
                                  Just d -> (all (isType s ctx) tys)
                                         && (tyArity d == length tys)
                                  Nothing -> False

lookupDecl :: TySymbol -> [Decl] -> Maybe Decl
lookupDecl _ []     = Nothing
lookupDecl s (d:ds) = case s == tySymbol d of
                        True -> Just d
                        False -> lookupDecl s ds


--------------------------------------------------------------------------------
--                              Check Type                                    --
--------------------------------------------------------------------------------

type Ctx = [(Variable,Type)]

lookupCons :: Symbol -> Signature -> Maybe (Decl,Data)
lookupCons sym [] = Nothing
lookupCons sym (d:ds) = case lookupCons' (datas d) of
                          Just dat -> Just (d,dat)
                          Nothing -> lookupCons sym ds
  where lookupCons' :: [Data] -> Maybe Data
        lookupCons' []  = Nothing
        lookupCons' (dat:dats) = case sym == dataSymbol dat of
                                   True -> Just dat
                                   False -> lookupCons' dats

-----------
-- infer --
-----------
infer :: Signature -> Ctx -> Term -> Type
infer _ _ (Lit _) = TyInt

infer s c (Add a b) =
  case check s c a TyInt && check s c b TyInt of
    True -> TyInt
    False -> error "both arguments of + expect an TyInt"

infer _ c (Var v) =
  case lookup v c of
    Just t -> t
    Nothing -> error ("variable " ++ show v ++ " not bound")

infer s c (Fix x t) = infer s c t

infer s c (App a b) =
  case infer s c a of
    TyArr tyDom tyCod ->
      case check s c b tyDom of
        True -> tyCod
        False -> error (show a ++ " expects arguments of type " ++ show tyDom)
    _ -> error ("operator must have a function type: " ++ show a)

infer s c (Cons sym ts) =
  case lookupCons sym s of
    Just (decl,dat) -> undefined
    Nothing -> error ("unknown constructor: " ++ show sym)

infer _ _ (Case _ _) = undefined

infer _ _ (Dest _ _) = undefined

infer _ _ (CoCase _) = undefined



-----------
-- check --
-----------
check :: Signature -> Ctx -> Term -> Type -> Bool
check _ _ (Lit _) TyInt = True
check s c (Add a b) TyInt = undefined
check _ c (Var v) ty =
  case lookup v c of
    Just ty' -> ty == ty'
    Nothing -> False
check _ _ (Fix _ _) _ = undefined
check _ _ (App _ _) _ = undefined
check _ _ (Cons sym ts) _ = undefined
check _ _ (Case _ _) _ = undefined
check _ _ (Dest _ _) _ = undefined
check _ _ (CoCase _) _ = undefined
check _ _ _ _ = False
