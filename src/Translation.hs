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

    -- ^ maps source type vars to target type vars
  , tyMap   :: [(D.TyVariable,Hs.TyVariable)]

    -- ^ maps source vars to target vars
  , vMap    :: [(D.Variable,Hs.Variable)]

    -- ^ maps destructors to contructors, their arity, and the index of the
    --   destructor in the constructor
  , destMap :: [(D.Variable,(Hs.Variable,Int,Int))]
  }
  deriving (Show,Eq)

startState :: TransST
startState = TransST 0 [] [] []

type TransM a = State TransST a

uniquify :: String -> TransM String
uniquify s =
  do { st <- get
     ; put (st { num = succ (num st) })
     ; return (s <> show (num st)) }

addTyAssoc :: D.TyVariable -> Hs.TyVariable -> TransM ()
addTyAssoc a b =
 do { st <- get
    ; put (st { tyMap = (a,b):(tyMap st) }) }

lookupTyAssoc :: D.TyVariable -> TransM (Maybe Hs.TyVariable)
lookupTyAssoc v = lookup v . tyMap <$> get

addDestAssoc :: D.Variable -> Hs.Variable -> Int -> Int -> TransM ()
addDestAssoc h k a i =
  do { st <- get
     ; put (st { destMap = (h,(k,a,i)):(destMap st)}) }

lookupDestAssoc :: D.Variable -> TransM (Maybe (Hs.Variable,Int,Int))
lookupDestAssoc h = lookup h . destMap <$> get

addVarAssoc :: D.Variable -> Hs.Variable -> TransM ()
addVarAssoc s t =
  do { st <- get
     ; put (st { vMap = (s,t):(vMap st)}) }



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
  do { tyvars <- translateTyVars (D.posTyFVars d)
     ; injs <- mapM translateInj (D.injections d)
     ; return (Hs.DataTyCons (D.posTyName d) tyvars injs) }

translateDecl (Left d) =
  do { tn <- uniquify (D.negTyName d)
     ; tyvars <- translateTyVars (D.negTyFVars d)
     ; let tnCons = "Mk" <> tn
           ty = foldl Hs.TyApp (Hs.TyVar tn) (map Hs.TyVar tyvars)
           arity = length . D.projections $ d
     ; (inj,_) <- foldrM (\p (accTy,i) ->
                           do { ty1 <- translateType . D.projCod $ p
                              ; addDestAssoc (D.projName p) tnCons arity i
                              ; return (Hs.TyArr ty1 accTy,succ i) })
                         (ty,1)
                         (D.projections d)
     ; return (Hs.DataTyCons tn tyvars [Hs.DataCon tnCons inj]) }

translateTyVars :: [D.TyVariable] -> TransM [Hs.TyVariable]
translateTyVars = mapM (\v -> do { v' <- uniquify v
                                 ; addTyAssoc v v'
                                 ; return v' })

translateInj :: D.Injection -> TransM Hs.DataCon
translateInj dinj = Hs.DataCon (D.injName dinj)
                <$> (translateType . D.injCod $ dinj)

-----------
-- Types --
-----------

translateType :: D.Type -> TransM Hs.Type
translateType D.TyInt       = return Hs.TyInt
translateType (D.TyArr a b) = Hs.TyArr <$> translateType a <*> translateType b
translateType (D.TyVar v)   = do { tm <- tyMap <$> get
                                 ; case lookup v tm of
                                     Just v' -> return (Hs.TyVar v')
                                     Nothing -> error ("Type variable '" <> v <> "' not in scope.")
                                 }
translateType (D.TyCons k)  = do { tm <- tyMap <$> get
                                 ; case lookup k tm of
                                     Just k' -> return (Hs.TyCons k')
                                     Nothing -> error ("Type constructor '" <> k <> "' not in scope.")
                                 }
translateType (D.TyApp a b) = Hs.TyApp <$> translateType a <*> translateType b

-----------
-- Terms --
-----------

translateTerm :: D.Term -> TransM Hs.Term
translateTerm (D.Lit i) = return (Hs.Lit i)
translateTerm (D.Add a b) = Hs.Add <$> translateTerm a <*> translateTerm b
translateTerm (D.Var v) =
  do { m <- vMap <$> get
     ; case lookup v m of
         Just v' -> return (Hs.Var v')
         Nothing -> error ("untranslated variable " <> v) }
translateTerm (D.Fix v t) = Hs.Fix <$> uniquify v  <*> translateTerm t
translateTerm (D.Cons k)      = Hs.Cons <$> uniquify k
translateTerm (D.Case t alts) = Hs.Case <$> translateTerm t
                                        <*> mapM (\(p,e) ->
                                                   do { p' <- translatePattern p
                                                      ; e' <- translateTerm e
                                                      ; return (p',e') })
                                                 alts
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

translateTerm (D.Dest h) =
  do { dmap <- destMap <$> get
     ; case lookup h dmap of
         Just (k,a,i) ->
           do { v <- uniquify "v"
              ; x <- uniquify "x"
              ; return (Hs.Lam v
                               (Hs.Case (Hs.Var v)
                                        [(Hs.PCons k (mkPatterns a i x)
                                         ,(Hs.Var x))]))
              }
         Nothing -> error ("cannot find destructor " <> h) }
  where mkPatterns :: Int -> Int -> Hs.Variable -> [Hs.Pattern]
        mkPatterns 0 _ _ = []
        mkPatterns a i x = case i == a of
                             True  -> Hs.PVar x : mkPatterns (pred a) i x
                             False -> Hs.PWild  : mkPatterns (pred a) i x


{- [Translating CoCase]
   Cocases get turned into constructors.

   ```
   cocase { Fst # -> 1, Snd # -> 2 }
   ```
   ===>
   ```
   mkNegPair 0 1
   ```
-}

translateTerm (D.CoCase coalts) = translateCoAlt (head coalts)
  where translateCoAlt :: (D.CoPattern,D.Term) -> TransM (Hs.Term)
        translateCoAlt (q,t) =
          case q of
            D.QHash -> translateTerm t
            D.QDest h _ ->
              do { mk <- lookupDestAssoc h
                 ; case mk of
                     Just (k,_,_) ->
                       do { t' <- translateTerm t
                          ; return (Hs.App (Hs.Cons k) t') }
                     Nothing -> error ("cannot find destructor" <> h)}
            D.QPat _ p ->
              do { v <- uniquify "v"
                 ; p' <- translatePattern p
                 ; t' <- translateTerm t
                 ; return (Hs.Lam v (Hs.Case (Hs.Var v) [(p',t')]))}

translatePattern :: D.Pattern -> TransM Hs.Pattern
translatePattern D.PWild        = return Hs.PWild
translatePattern (D.PVar v)     = do { v' <- uniquify v
                                     ; addVarAssoc v v'
                                     ; return (Hs.PVar v') }
translatePattern (D.PCons k ps) = Hs.PCons <$> uniquify k
                                           <*> mapM translatePattern ps
