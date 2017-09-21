{-# LANGUAGE MultiParamTypeClasses #-}
module Translation where

import Control.Monad.State
import Data.Monoid ((<>))
import Data.Foldable (foldrM)
import Debug.Trace

import qualified DualSyn as D
import qualified HsSyn as Hs
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

translateProgramST :: D.Program -> Hs.Program
translateProgramST dpgm =
  fst $ runState
  (do { decls <- mapM transDeclST (D.pgmDecls dpgm)
      ; let ft = D.flattenPatterns . D.pgmTerm $ dpgm
      ; term  <- trace (pp ft) $ transTermST ft
      ; return (Hs.Pgm decls term) })
  startState

translateProgramLocal :: D.Program -> Hs.Program
translateProgramLocal dpgm = Hs.Pgm (fmap transDeclL . D.pgmDecls $ dpgm)
                                    ( transTermL . D.flattenPatterns . D.pgmTerm
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
  do { tn <- uniquify (D.posTyName d)
     ; addTyAssoc (D.posTyName d) tn
     ; tyvars <- transTyVarsST (D.posTyFVars d)
     ; injs <- mapM transInjST (D.injections d)
     ; return (Hs.DataTyCons tn tyvars injs) }

transDeclST (Left d) =
  do { tn <- uniquify (D.negTyName d)
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
transTyVarsST = mapM (\v -> do { v' <- uniquify v
                               ; addTyAssoc v v'
                               ; return v' })

transInjST :: D.Injection -> TransM Hs.DataCon
transInjST dinj =
  do { n <- uniquify (D.injName dinj)
     ; addVarAssoc (D.injName dinj) n
     ; ty <- transTypeST . D.injCod $ dinj
     ; return (Hs.DataCon n ty) }

-----------
-- Local --
-----------

transDeclL :: D.Decl -> Hs.DataTyCons
transDeclL = undefined

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

transTermST :: D.Term D.FlatP D.FlatQ -> TransM Hs.Term
transTermST (D.Lit i) = return (Hs.Lit i)
transTermST (D.Add a b) = Hs.Add <$> transTermST a <*> transTermST b
transTermST (D.Var v) =
  do { m <- lookupVar v
     ; case m of
         Just v' -> return (Hs.Var v')
         Nothing -> do { vm <- vMap <$> get
                       ; error ("untranslated variable " <> v
                               <> "\nin: " <> show vm) }
     }
transTermST (D.Fix v t) = undefined
  -- do { v' <- uniquify v
  --    ; addVarAssoc v v'
  --    ; Hs.Fix v' <$> translateTerm t }
transTermST (D.Cons k) =
  do { m <- vMap <$> get
     ; case lookup k m of
         Just k' -> return (Hs.Cons k')
         Nothing -> error ("untranslated constructor " <> k) }
transTermST (D.Case t alts) =
  Hs.Case <$> transTermST t
          <*> mapM (\(p,e) ->
                      do { p' <- transPatternST p
                         ; _ <- error  . show . vMap <$> get
                         ; e' <- transTermST e
                         ; return (p',e') })
                                                 alts
transTermST (D.App a b) = Hs.App <$> transTermST a <*> transTermST b

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

transTermST (D.Dest h) =
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

transTermST (D.CoCase coalts) = translateCoAlt (head coalts)
  where translateCoAlt :: (D.FlatQ, D.Term D.FlatP D.FlatQ)
                       -> TransM Hs.Term
        translateCoAlt (q,t) =
          case q of
            D.FQHead -> transTermST t
            D.FQDest h ->
              do { mk <- lookupDestAssoc h
                 ; case mk of
                     Just (k,_,_) ->
                       do { t' <- transTermST t
                          ; return (Hs.App (Hs.Cons k) t') }
                     Nothing -> error ("cannot find destructor" <> h)}
            D.FQPat p ->
              do { v <- uniquify "v"
                 ; p' <- transPatternST p
                 ; t' <- transTermST t
                 ; return (Hs.Lam v (Hs.Case (Hs.Var v) [(p',t')]))}

transPatternST :: D.FlatP -> TransM Hs.Pattern
transPatternST D.FPWild = return Hs.PWild
transPatternST (D.FPVar v) =
  do { v' <- uniquify v
     ; addVarAssoc v v'
     ; return (Hs.PVar v') }
transPatternST (D.FPCons k vs) =
  do { m <- vMap <$> get
     ; case lookup k m of
         Just k' -> do { vs' <- forM vs $ \v ->
                                  do { v' <- uniquify v
                                     ; addVarAssoc v v'
                                     ; return v' }
                       ; return (Hs.PCons k' vs') }
         Nothing -> error (  "untranslated constructor " <> k
                          <> " in pattern" <> show (D.FPCons k vs)) }

-----------
-- Local --
-----------

transTermL :: D.Term D.FlatP D.FlatQ -> Hs.Term
transTermL = undefined
