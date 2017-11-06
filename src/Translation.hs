{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

import Control.Monad.State
import Data.Monoid ((<>))
import Data.Foldable (foldrM)
import Debug.Trace

import qualified Syntax.Dual as D
import qualified Syntax.Hs as Hs
import qualified Syntax.ML as ML
import Syntax.Variable
import Pretty

--------------------------------------------------------------------------------
--                            Translation Monad                               --
--------------------------------------------------------------------------------
{- Translation is done in the context of a translation monad which at the least
requires unique identifiers. -}

data TransST
  = TransST
  { num     :: Int -- ^ tracks unique variable creation

    -- ^ maps source type vars to target type vars
  , tyMap   :: [(Variable,Variable)]

    -- ^ maps source vars to target vars
  , vMap    :: [(Variable,Variable)]

    -- ^ maps destructors to contructors, their arity, and the index of the
    --   destructor in the constructor
  , destMap :: [(Variable,(Variable,Int,Int))]
  }
  deriving (Show,Eq)

startState :: TransST
startState = TransST 0 [] [] []

type TransM a = State TransST a

freshen :: String -> TransM String
freshen s =
  do { st <- get
     ; put (st { num = succ (num st) })
     ; return (s <> show (num st)) }

addTyAssoc :: Variable -> Variable -> TransM ()
addTyAssoc a b =
 do { st <- get
    ; put (st { tyMap = (a,b):(tyMap st) }) }

lookupTyAssoc :: Variable -> TransM (Maybe Variable)
lookupTyAssoc v = lookup v . tyMap <$> get

addDestAssoc :: Variable -> Variable -> Int -> Int -> TransM ()
addDestAssoc h k a i =
  do { st <- get
     ; put (st { destMap = (h,(k,a,i)):(destMap st)}) }

lookupDestAssoc :: Variable -> TransM (Maybe (Variable,Int,Int))
lookupDestAssoc h = lookup h . destMap <$> get

addVarAssoc :: Variable -> Variable -> TransM ()
addVarAssoc s t =
  do { st <- get
     ; put (st { vMap = (s,t):(vMap st)}) }

lookupVar :: Variable -> TransM (Maybe Variable)
lookupVar v = lookup v . vMap <$> get

--------------------------------------------------------------------------------
--                                Top Level                                   --
--------------------------------------------------------------------------------
{- Here we present two translations: `translateProgramST` and
`translateProgramLocal`. `translateProgramST` is stateful in that the
translation of some term is dependent on the translation of of the
declaration. `translateProgramLocal` infers a naming convention to avoid the
dependence of terms on declarations.
-}

translateProgramST :: D.Program D.FlatTerm -> Hs.Program
translateProgramST dpgm =
  fst $ runState
  (do { decls <- mapM (fmap Left . transDeclST) (D.pgmDecls dpgm)
      ; let ft = D.pgmTerm $ dpgm
      ; term  <- transTermST ft
      ; return (Hs.Pgm decls term) })
  startState

{- Local translation defines new functions when a declaration is transformed.
These functions must be in scope for the term. -}
translateProgramLocal :: D.Program D.FlatTerm -> Hs.Program
translateProgramLocal dpgm =
  let (f,decls') = foldr (\d (f,ds) ->
                           let (df,d') = transDeclL d
                           in  (df . f, d':ds) )
                         (id,[])
                         (D.pgmDecls dpgm)
  in Hs.Pgm decls'
            ( f . transTermL . D.pgmTerm $ dpgm )

translateProgramCBV :: D.Program D.FlatTerm -> ML.Program
translateProgramCBV dpgm = ML.Pgm ( fmap transDeclCBV . D.pgmDecls $ dpgm )
                                  ( transTermCBV
                                  . D.pgmTerm
                                  $ dpgm )

--------------------------------------------------------------------------------
--                              Declarations                                  --
--------------------------------------------------------------------------------
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

--------------
-- Stateful --
--------------

transDeclST :: D.Decl -> TransM Hs.DataTyCons
transDeclST (Right d) =
  do { tn <- freshen (D.posTyName d)
     ; addTyAssoc (D.posTyName d) tn
     ; tyvars <- transTyVarsST (D.posTyFVars d)
     ; injs <- mapM transInjST (D.injections d)
     ; return (Hs.DataTyCons tn tyvars injs) }

transDeclST (Left d) =
  do { tn <- freshen (D.negTyName d)
     ; tyvars <- transTyVarsST (D.negTyFVars d)
     ; let tnCons = "Mk" <> tn
           ty = foldl Hs.TyApp (Hs.TyVar tn) (map Hs.TyVar tyvars)
           arity = length . D.projections $ d
     ; (inj,_) <- foldrM (\p (accTy,i) ->
                           do { ty1 <- transTypeST . D.projCod $ p
                              ; addDestAssoc (D.projName p) tnCons arity i
                              ; return (Hs.TyArr ty1 accTy,succ i) })
                         (ty,1)
                         (D.projections d)
     ; return (Hs.DataTyCons tn tyvars [Hs.DataCon tnCons inj]) }

transTyVarsST :: [Variable] -> TransM [Variable]
transTyVarsST = mapM (\v -> do { v' <- freshen v
                               ; addTyAssoc v v'
                               ; return v' })

transInjST :: D.Injection -> TransM Hs.DataCon
transInjST dinj =
  do { n <- freshen (D.injName dinj)
     ; addVarAssoc (D.injName dinj) n
     ; ty <- transTypeST . D.injCod $ dinj
     ; return (Hs.DataCon n ty) }

-----------
-- Local --
-----------

transDeclL
  :: D.Decl
  -> (Hs.Term -> Hs.Term, Either Hs.DataTyCons Hs.RecordTyCons)
transDeclL (Right d) =
  (id, Left (Hs.DataTyCons (D.posTyName d)
                           (D.posTyFVars d)
                           (fmap mkDataCon . D.injections $ d)))
  where mkDataCon :: D.Injection -> Hs.DataCon
        mkDataCon inj = Hs.DataCon (D.injName inj) (transTypeL . D.injCod $ inj)

transDeclL (Left d)  =
  ( addSetters (D.projections d) 0
  , Right (Hs.RecordTyCons name
                           (D.negTyFVars d)
                           (fmap mkRecordField (D.projections d))))
  where name = "Mk" <> D.negTyName d
        pname p = "_" <> D.projName p

        numProjs = length . D.projections $ d

        -- an association between projections and their index
        pIndexAssoc :: [(Int,D.Projection)]
        pIndexAssoc = foldrWithIndex (\i p a -> (i,p):a) [] (D.projections d)

        addSetters :: [D.Projection] -> Int -> (Hs.Term -> Hs.Term)
        addSetters [] _ = id
        addSetters (p:ps) i =
          (Hs.Let
            setterName
            (Hs.Lam "d"
              (Hs.Lam "x"
                (foldlWithIndex (\j c p ->
                                  let t = case i == j of
                                            True  -> Hs.Var "x"
                                            False -> Hs.App (Hs.Var (pname p))
                                                            (Hs.Var "d")
                                  in Hs.App c t
                                )
                                (Hs.Cons name)
                                (D.projections d))))) --Hs.App(Hs.App (Hs.Cons name) (Hs.Var "x"))))))
          . (addSetters ps (i+1))
          where setterName = "set_" <> D.projName p

        mkRecordField :: D.Projection -> Hs.Field
        mkRecordField p = Hs.Field (pname p)
                                   (transTypeL . D.projCod $ p)

foldrWithIndex :: (Int -> a -> b -> b) -> b -> [a] -> b
foldrWithIndex f b = snd . foldr (\a (i,x) -> (i+1,f i a x)) (0,b)

foldlWithIndex :: (Int -> b -> a -> b) -> b -> [a] -> b
foldlWithIndex f b = snd . foldl (\(i,x) a -> (i+1,f i x a)) (0,b)

-------------------
-- Call-by-value --
-------------------

transDeclCBV :: D.Decl -> ML.DataTyCons
transDeclCBV = error "TODO: transDeclCBV{}"

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

--------------
-- Stateful --
--------------
{- Type translation is trivial, the only note is that type variables and
constructors depend on the translation of declarations and must lookup their
value in the TransM monad. -}

transTypeST :: D.Type -> TransM Hs.Type
transTypeST D.TyInt       = return Hs.TyInt
transTypeST (D.TyArr a b) = Hs.TyArr <$> transTypeST a <*> transTypeST b
transTypeST (D.TyApp a b) = Hs.TyApp <$> transTypeST a <*> transTypeST b
transTypeST (D.TyVar v)   =
  do { tm <- tyMap <$> get
     ; case lookup v tm of
         Just v' -> return (Hs.TyVar v')
         Nothing -> error ("Type variable '" <> v <> "' not in scope.")
     }
transTypeST (D.TyCons k)  =
  do { tm <- tyMap <$> get
     ; case lookup k tm of
         Just k' -> return (Hs.TyCons k')
         Nothing -> error ("Type constructor '" <> k <> "' not in scope.")
     }

-----------
-- Local --
-----------

transTypeL :: D.Type -> Hs.Type
transTypeL D.TyInt       = Hs.TyInt
transTypeL (D.TyArr a b) = Hs.TyArr (transTypeL a) (transTypeL b)
transTypeL (D.TyApp a b) = Hs.TyApp (transTypeL a) (transTypeL b)
transTypeL (D.TyVar v)   = Hs.TyVar v
transTypeL (D.TyCons k)  = Hs.TyCons k

--------------------------------------------------------------------------------
--                                  Terms                                     --
--------------------------------------------------------------------------------

--------------
-- Stateful --
--------------

transTermST :: D.FlatTerm -> TransM Hs.Term
transTermST (D.FLet v a b) =
  do { v' <- freshen v
     ; addVarAssoc  v v'
     ; a' <- transTermST a
     ; b' <- transTermST b
     ; return (Hs.Let v' a' b') }

transTermST (D.FLit i) = return (Hs.Lit i)
transTermST (D.FAdd a b) = Hs.Add <$> transTermST a <*> transTermST b
transTermST (D.FVar v) =
  do { m <- lookupVar v
     ; case m of
         Just v' -> return (Hs.Var v')
         Nothing -> do { vm <- vMap <$> get
                       ; error ("untranslated variable " <> v
                               <> "\nin: " <> show vm) }
     }
transTermST (D.FFix v t) = undefined
  -- do { v' <- freshen v
  --    ; addVarAssoc v v'
  --    ; Hs.Fix v' <$> translateTerm t }
transTermST (D.FCons k) =
  do { m <- vMap <$> get
     ; case lookup k m of
         Just k' -> return (Hs.Cons k')
         Nothing -> error ("untranslated constructor " <> k) }
transTermST (D.FCase t alt _) =
  Hs.Case <$> transTermST t
          <*> ((\(p,e) ->
                      do { p' <- transPatternST p
                         ; _ <- error  . show . vMap <$> get
                         ; e' <- transTermST e
                         ; return [(p',e')] })
              $  alt )
transTermST (D.FApp a b) = Hs.App <$> transTermST a <*> transTermST b

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

transTermST (D.FDest h) =
  do { dmap <- destMap <$> get
     ; case lookup h dmap of
         Just (k,a,i) ->
           do { v <- freshen "v"
              ; x <- freshen "x"
              ; return (Hs.Lam v
                               (Hs.Case (Hs.Var v)
                                        [(Hs.PCons k (mkPatterns a i x)
                                         ,(Hs.Var x))]))
              }
         Nothing -> error ("cannot find destructor " <> h) }
  where mkPatterns :: Int -> Int -> Variable -> [Variable]
        mkPatterns 0 _ _ = []
        mkPatterns a i x = case i == a of
                             True  -> x : mkPatterns (pred a) i x
                             False -> "_"  : mkPatterns (pred a) i x -- this is a lazy,dirty,nasty,ugly hack


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

transTermST (D.FCoCase coalt _) = translateCoAlt coalt
  where translateCoAlt :: (D.FlatCopattern, D.FlatTerm)
                       -> TransM Hs.Term
        translateCoAlt (q,t) =
          case q of
            D.FlatCopDest h ->
              do { mk <- lookupDestAssoc h
                 ; case mk of
                     Just (k,_,_) ->
                       do { t' <- transTermST t
                          ; return (Hs.App (Hs.Cons k) t') }
                     Nothing -> error ("cannot find destructor" <> h)}
            D.FlatCopPat p ->
              do { v <- freshen "v"
                 ; p' <- transPatternST p
                 ; t' <- transTermST t
                 ; return (Hs.Lam v (Hs.Case (Hs.Var v) [(p',t')]))}

transTermST (D.FFail) = return Hs.Fail

transPatternST :: D.FlatPattern -> TransM Hs.Pattern
transPatternST (D.FlatPatVar v) =
  do { v' <- freshen v
     ; addVarAssoc v v'
     ; return (Hs.PVar v') }
transPatternST (D.FlatPatCons k vs) =
  do { m <- vMap <$> get
     ; case lookup k m of
         Just k' -> do { vs' <- forM vs $ \v ->
                                  do { v' <- freshen v
                                     ; addVarAssoc v v'
                                     ; return v' }
                       ; return (Hs.PCons k' vs') }
         Nothing -> error (  "untranslated constructor " <> k
                          <> " in pattern" <> show (D.FlatPatCons k vs)) }

-----------
-- Local --
-----------

transTermL :: D.FlatTerm -> Hs.Term
transTermL (D.FLet v a b) = Hs.Let v (transTermL a) (transTermL b)
transTermL (D.FLit i) = Hs.Lit i
transTermL (D.FAdd a b) = Hs.Add (transTermL a) (transTermL b)
transTermL (D.FVar v) = Hs.Var v
transTermL (D.FFix v a) = let a' = transTermL a in Hs.Let v a' a'
transTermL (D.FApp a b) = Hs.App (transTermL a) (transTermL b)
transTermL (D.FCons k) = Hs.Cons k
transTermL (D.FCase t (p,u) d) = Hs.Case (transTermL t)
                                         [(transPatL p, transTermL u)
                                         ,(Hs.PWild,transTermL d)]
transTermL (D.FDest h) = Hs.Var ("_" <> h)
transTermL (D.FCoCase (q,u) d) = transCoaltL (q,u) (transTermL d)
transTermL (D.FFail) = Hs.Fail

transPatL :: D.FlatPattern -> Hs.Pattern
transPatL (D.FlatPatVar v)     = Hs.PVar v
transPatL (D.FlatPatCons k vs) = Hs.PCons k vs

transCoaltL :: (D.FlatCopattern, D.FlatTerm) -> Hs.Term -> Hs.Term
transCoaltL (D.FlatCopDest h,u) t = Hs.App (Hs.App (Hs.Var ("set_" <> h)) t)
                                           (transTermL u)
transCoaltL (D.FlatCopPat _,u) _ = transTermL u

-------------------
-- Call-by-value --
-------------------

transTermCBV :: D.FlatTerm -> ML.Term
transTermCBV (D.FLit i) = ML.Lit i
