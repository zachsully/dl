module Judgement where

import DualSyn

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

typeOfProgram :: Program -> Type
typeOfProgram (Pgm decls term) = infer decls [] term

--------------------------------------------------------------------------------
--                                isType                                      --
--------------------------------------------------------------------------------
{- Checks whether a type is well formed -}

isType :: [Decl]              -- ^ A set of type signatures
       -> [(TyVariable,Type)] -- ^ A context of bindings of type variables
       -> Type
       -> Bool
isType _ ctx TyInt         = True
isType s ctx (TyArr a b)   = isType s ctx a && isType s ctx b
isType s ctx (TyVar v)     = case lookup v ctx of
                               Just t -> isType s ctx t
                               Nothing -> False

{- A standalone type constructor is only valid if its arity is 0 -}
isType s ctx (TyCons tc)   = case lookupDecl tc s of
                               Just d -> declArity d == 0
                               Nothing -> False
isType s ctx ty@(TyApp a b) = case collectTyArgs ty of
                               Just (tc,tys) ->
                                 case lookupDecl tc s of
                                   Just d -> (all (isType s ctx) tys)
                                          && (length tys == declArity d)
                                   Nothing -> False
                               Nothing -> False

lookupDecl :: TyVariable -> [Decl] -> Maybe Decl
lookupDecl _ [] = Nothing
lookupDecl v ((Left d):ds) = case v == negTyName d of
                               True -> Just (Left d)
                               False -> lookupDecl v ds
lookupDecl v ((Right d):ds) = case v == posTyName d of
                               True -> Just (Right d)
                               False -> lookupDecl v ds

--------------------------------------------------------------------------------
--                              Check Type                                    --
--------------------------------------------------------------------------------

type Ctx = [(Variable,Type)]

-- lookupCons :: Symbol -> [Decl] -> Maybe (Decl,Injection)
-- lookupCons sym [] = Nothing
-- lookupCons sym (d:ds) = case lookupCons' (datas d) of
--                           Just dat -> Just (d,dat)
--                           Nothing -> lookupCons sym ds
--   where lookupCons' :: [Data] -> Maybe Data
--         lookupCons' []  = Nothing
--         lookupCons' (dat:dats) = case sym == dataSymbol dat of
--                                    True -> Just dat
--                                    False -> lookupCons' dats

-----------
-- infer --
-----------
infer :: [Decl] -> Ctx -> Term -> Type
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

infer s c (Cons k) = error "infer{Cons}"
infer s c (Dest h) = error "infer{Dest}"

infer s c (App a b) =
  case infer s c a of
    TyArr tyDom tyCod ->
      case check s c b tyDom of
        True -> tyCod
        False -> error (show a ++ " expects arguments of type " ++ show tyDom)
    _ -> error ("operator must have a function type: " ++ show a)

infer _ _ (Case _ _) = error "infer{Case}"

infer _ _ (CoCase _) = error "infer{CoCase}"

-----------
-- check --
-----------

check :: [Decl] -> Ctx -> Term -> Type -> Bool
check _ _ (Lit _)   TyInt = True
check s c (Add a b) TyInt = check s c a TyInt && check s c b TyInt
check _ c (Var v)   ty    = case lookup v c of
                              Just ty' -> ty == ty'
                              Nothing -> False
check s c (Fix v t)  ty   = check s ((v,ty):c) t ty
check _ _ (Cons _)   _    = error "check{Cons}"
check _ _ (Dest _)   _    = error "check{Dest}"
check _ _ (App _ _)  ty   = undefined
check _ _ (Case _ _) _    = undefined
check _ _ (CoCase _) _    = undefined
check _ _ _ _ = False
