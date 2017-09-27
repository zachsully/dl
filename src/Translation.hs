{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

import Control.Monad.State
import Data.Monoid ((<>))
import Data.Foldable (foldrM)
import Debug.Trace

import qualified DualSyn as D
import qualified HsSyn as Hs
import qualified MLSyn as ML
import Utils

{- A lot of the translation is boilerplate. We use separate syntax for DualSyn
and HsSyn to make explicit what is happening even though the former is a subset
of the latter.

   Translation is done in the context of a translation monad which keeps track
of unique identifiers.
-}


--------------------------------------------------------------------------------
--                            Translation Monad                               --
--------------------------------------------------------------------------------

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

freshen :: String -> TransM String
freshen s =
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

lookupVar :: D.Variable -> TransM (Maybe Hs.Variable)
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

translateProgramST :: D.Program D.Term -> Hs.Program
translateProgramST dpgm =
  fst $ runState
  (do { decls <- mapM transDeclST (D.pgmDecls dpgm)
      ; let ft = D.flatten . D.pgmTerm $ dpgm
      ; term  <- transTermST ft
      ; return (Hs.Pgm decls term) })
  startState

translateProgramLocal :: D.Program D.Term -> Hs.Program
translateProgramLocal dpgm = Hs.Pgm (fmap transDeclL . D.pgmDecls $ dpgm)
                                    ( transTermL
                                    . D.flatten
                                    . D.pgmTerm
                                    $ dpgm )

translateProgramCBV :: D.Program D.Term -> ML.Program
translateProgramCBV dpgm = ML.Pgm ( fmap transDeclCBV . D.pgmDecls $ dpgm )
                                  ( transTermCBV
                                  . D.flatten
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

transTyVarsST :: [D.TyVariable] -> TransM [Hs.TyVariable]
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

transDeclL :: D.Decl -> Hs.DataTyCons
transDeclL (Right d) = Hs.DataTyCons (D.posTyName d) (D.posTyFVars d) undefined
transDeclL (Left d)  = Hs.DataTyCons (D.negTyName d) (D.negTyFVars d) undefined


-------------------
-- Call-by-value --
-------------------

transDeclCBV :: D.Decl -> ML.DataTyCons
transDeclCBV = undefined

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
  where mkPatterns :: Int -> Int -> Hs.Variable -> [Hs.Variable]
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
transTermL (D.FCase t alts _) = undefined
transTermL (D.FDest h) = Hs.Var ("obs" <> h)
transTermL (D.FCoCase coalts _) = undefined

transAltL :: (D.FlatPattern,D.FlatTerm) -> (Hs.Pattern,Hs.Term)
transAltL = error "transAltL{*}"

transCoaltL :: (D.FlatCopattern, D.FlatTerm) -> Hs.Term
transCoaltL (D.FlatCopDest _,u) = transTermL u
transCoaltL (D.FlatCopPat _,u) = transTermL u

-------------------
-- Call-by-value --
-------------------

transTermCBV :: D.FlatTerm -> ML.Term
transTermCBV (D.FLit i) = ML.Lit i
