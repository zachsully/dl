{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

import Control.Monad.State
import Data.Monoid ((<>))
import Data.Foldable (foldrM)

import qualified DualSyn as D
import qualified HsSyn as Hs

{- A lot of the translation is boilerplate. We use separate syntax for DualSyn
   and HsSyn to make explicit what is happening even though the former is a
   subset of the latter.

   Translation is done in the context of a translation monad which keeps track
   of unique identifiers.
-}

data TransST
  = TransST
  { num     :: Int -- ^ tracks unique variable creation

    -- ^ maps freevars to freevars
  , tyMap   :: [(D.TyVariable,Hs.TyVariable)]

    -- ^ maps destructors to contructors, their arity, and the index of the
    --   destructor in the constructor
  , destMap :: [(D.Variable,(Hs.Variable,Int,Int))]}
  deriving (Show,Eq)

startState :: TransST
startState = TransST 0 [] []

type TransM a = State TransST a

uniquify :: String -> TransM String
uniquify s =
  do { st <- get
     ; put (st { num = succ (num st) })
     ; return (s <> "_" <> show (num st)) }

addDestAssoc :: D.Variable -> Hs.Variable -> TransM ()
addDestAssoc h k =
  do { st <- get
     ; put (st { destMap = (h,(k,0,0)):(destMap st)}) }

---------------
-- Top Level --
---------------

translateProgram :: D.Program -> Hs.Program
translateProgram dpgm = fst $ runState
                        (do { decls <- mapM translateDecl (D.pgmDecls dpgm)
                            ; term  <- translateTerm (D.pgmTerm dpgm)
                            ; return (Hs.Pgm decls term) })
                        startState

{- Translating positive data is just the identity function.

   Translating negative data generates a new positive type with a single
   constructor containing fields for each projection. Condsider the negative
   pair type:

   ```
   codata NegPair A B
     { Fst : NegPair A B -> A
     , Snd : NegPair A B -> B }
   ```
   ===>
   ```
   data NegPair A B
     { mkNegPair : A -> B -> NegPair A B }
   ```

   We need to keep track of which index in the new positive datatype which
   projection from the old type is associated with for use with destructors. We
   need to keep track of the constructor for use with cocase.

   ```
   cocase { Fst # -> 0, Snd # -> 1 }
   ```
   ===>
   ```
   mkNegPair 0 1
   ```
-}
translateDecl :: D.Decl -> TransM Hs.DataTyCons
translateDecl (Right d) =
  Hs.DataTyCons (D.posTyName d) (D.posTyFVars d)
     <$> mapM translateInj (D.injections d)

translateDecl (Left d) =
  do { tn <- uniquify (D.negTyName d)
     ; let tnCons = "mk" <> tn
           ty = foldl Hs.TyApp (Hs.TyVar tn) (map Hs.TyVar . D.negTyFVars $ d)
     ; inj <- foldrM (\p accTy ->
                       do { ty1 <- translateType . D.projCod $ p
                          ; return (Hs.TyArr ty1 accTy) })
                     ty
                     (D.projections d)
     ; return (Hs.DataTyCons tn (D.negTyFVars d) [Hs.DataCon tnCons inj]) }
  --   Hs.DataCon tc
  --              (foldr Hs.TyArr into (map (translateType . D.projCod) ps))
  -- where into = foldl Hs.TyApp (Hs.TyVar tc) (map Hs.TyVar fvars)

translateInj :: D.Injection -> TransM Hs.DataCon
translateInj dinj = Hs.DataCon (D.injName dinj)
                <$> (translateType . D.injCod $ dinj)

data Proj'
  = Proj'
  { name  :: Hs.Variable
  , arity :: Int
  , index :: Int }
  deriving Show


-----------
-- Types --
-----------

translateType :: D.Type -> TransM Hs.Type
translateType D.TyInt       = return Hs.TyInt
translateType (D.TyArr a b) = Hs.TyArr <$> translateType a <*> translateType b
translateType (D.TyVar v)   = Hs.TyVar <$> uniquify v
translateType (D.TyCons k)  = Hs.TyCons <$> uniquify k
translateType (D.TyApp a b) = Hs.TyApp <$> translateType a <*> translateType b

-----------
-- Terms --
-----------

translateTerm :: D.Term -> TransM Hs.Term
translateTerm (D.Lit i)       = return (Hs.Lit i)
translateTerm (D.Add a b)     = Hs.Add <$> translateTerm a
                                       <*> translateTerm b
translateTerm (D.Var v)       = Hs.Var <$> uniquify v
translateTerm (D.Fix v t)     = Hs.Fix <$> uniquify v
                                       <*> translateTerm t
translateTerm (D.Cons k)      = Hs.Cons <$> uniquify k
translateTerm (D.Case t alts) = Hs.Case <$> translateTerm t
                                        <*> mapM (\(p,e) ->
                                                   do { p' <- translatePattern p
                                                      ; e' <- translateTerm e
                                                      ; return (p',e') })
                                                 alts
  where translatePattern :: D.Pattern -> TransM Hs.Pattern
        translatePattern D.PWild        = return Hs.PWild
        translatePattern (D.PVar v)     = Hs.PVar <$> uniquify v
        translatePattern (D.PCons k ps) = Hs.PCons <$> uniquify k
                                                   <*> mapM translatePattern ps
translateTerm (D.App a b)     = Hs.App <$> translateTerm a
                                       <*> translateTerm b

{- THE INTERESTING CASES
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
(\x -> case x of
         Pair _ x' ->
           case x' of
             Pair x'' _ -> x'')
(Pair 0 (Pair 1 2))
```

-}

translateTerm (D.Dest s) = return $
  case lookup s (error "translateTerm{Dest}") of
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


{- [Translating CoCase]
   Cocases get turned into constructors.
-}
translateTerm (D.CoCase coalts) = (getCons coalts)
  where getCons :: [(D.CoPattern,D.Term)] -> TransM (Hs.Term)
        getCons [] = error "cannot determine the type of empty cocase"
        getCons ((q,t):_) =
          case q of
            D.Hash -> error "translateTerm{CoCase.QHash}"
            D.QDest h _ -> do { dmap <- destMap <$> get
                              ; case lookup h dmap of
                                  Just (k,_,_) -> return (Hs.Cons k)
                                  Nothing -> error ("cannot find destructor " <> h) }
            D.QPat _ _ -> error "translateTerm{CoCase.QPat}"
