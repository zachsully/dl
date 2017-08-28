{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

import Control.Arrow ((***))

import qualified DualSyn as D
import qualified HsSyn as Hs

{- A lot of the translation is boilerplate. We use separate syntax for DualSyn
   and HsSyn to make explicit what is happening even though the former is a
   subset of the latter.
-}

---------------
-- Top Level --
---------------

translateProgram :: D.Program -> Hs.Program
translateProgram dpgm = Hs.Pgm (map translateDecl . D.pgmDecls $ dpgm)
                               (translateTerm [] . D.pgmTerm $ dpgm)

translateDecl :: D.Decl -> Hs.DataTyCons
translateDecl (Right d) = Hs.DataTyCons (D.posTyName d)
                                        (D.posTyFVars d)
                                        (map translateInj . D.injections $ d)
translateDecl (Left d) = Hs.DataTyCons (D.negTyName d)
                                       (D.negTyFVars d)
                                       [ collectProjs (D.negTyName d)
                                                      (D.negTyFVars d)
                                         . D.projections $ d]

translateInj :: D.Injection -> Hs.DataCon
translateInj dinj = Hs.DataCon (D.injName dinj) (translateType . D.injCod $ dinj)

collectProjs :: Hs.TyVariable -> [Hs.TyVariable] -> [D.Projection] -> Hs.DataCon
collectProjs tc fvars ps =
    Hs.DataCon tc
               (foldr Hs.TyArr into (map (translateType . D.projCod) ps))
  where into = foldl Hs.TyApp (Hs.TyVar tc) (map Hs.TyVar fvars)

data Proj'
  = Proj'
  { name  :: Hs.Variable
  , arity :: Int
  , index :: Int }
  deriving Show


-----------
-- Types --
-----------

translateType :: D.Type -> Hs.Type
translateType D.TyInt = Hs.TyInt
translateType (D.TyArr a b) = Hs.TyArr (translateType a) (translateType b)
translateType (D.TyVar v) = Hs.TyVar v
translateType (D.TyCons k) = Hs.TyCons k
translateType (D.TyApp a b) = Hs.TyApp (translateType a) (translateType b)

-----------
-- Terms --
-----------

translateTerm :: [(Hs.Variable,Proj')] -> D.Term -> Hs.Term
translateTerm _ (D.Lit i) = Hs.Lit i
translateTerm env (D.Add a b) = Hs.Add (translateTerm env a)
                                       (translateTerm env b)
translateTerm _ (D.Var v) = Hs.Var v
translateTerm env (D.Fix v t) = Hs.Fix v (translateTerm env t)
translateTerm _ (D.Cons k) = Hs.Cons k
translateTerm env (D.Case t alts) = Hs.Case (translateTerm env t)
                                            (map (translatePattern *** translateTerm env) alts)
translateTerm env (D.App a b) = Hs.App (translateTerm env a) (translateTerm env b)

-- The interesting cases
{-
Consider the following example:

```
Fst (Snd (cocase { Fst #       -> 0
                 , Fst (Snd #) -> 1
                 , Snd (Snd #) -> 2 }))
```

There are two import things to compile here, both the destructor application
and the cocase expression.

The cocase ends up just constructing the complete value:

```
x = Pair 0 (Pair 1 2)
```

Since we are compiling to a lazy language this is not actually done until we
demand values by applying our projections. In order to project out a value
we do a case statement which evaluates up until we hit the pair constructor.
We then use the constructor generated from translating the data type, binding
the variable we want to project and using wildcards for the other patterns. We
just return the bound variable.

```
case x of
  Pair _ x' ->
    case x' of
      Pair x'' _ -> x''
```

-}

translateTerm env (D.Dest s) =
  case lookup s env of
    Just proj' -> Hs.Lam "x" (Hs.Case (Hs.Var "x")
                                      [( Hs.PCons (name proj')
                                                  (mkPatterns (index proj')
                                                              (arity proj'))
                                       , (Hs.Var "x'"))])
    Nothing -> error "destructor not found"
  where mkPatterns :: Int -> Int -> [Hs.Pattern]
        mkPatterns _ 0 = []
        mkPatterns i a = case i == a of
                           True  -> Hs.PVar "x" : mkPatterns i (pred a)
                           False -> Hs.PWild    : mkPatterns i (pred a)


translateTerm _ (D.CoCase _) = undefined

translatePattern :: D.Pattern -> Hs.Pattern
translatePattern D.PWild = Hs.PWild
translatePattern (D.PVar v) = Hs.PVar v
translatePattern (D.PCons k ps) = Hs.PCons k (map translatePattern ps)
