{-# LANGUAGE GADTs, KindSignatures, LambdaCase #-}
module DL.Syntax.Flat
  ( FlatTerm (..)
  , FlatPattern (..)
  , FlatObsCtx (..)
  , flattenPgm
  , flatten
  ) where

import Control.Monad.State
import Data.Monoid ((<>))
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Variable
import DL.Pretty

--------------------------------------------------------------------------------
--                              Flat Terms                                    --
--------------------------------------------------------------------------------
{- FlatTerms where added because in addition to having only flat (co)patterns,
they also have (co)case statements that contain defaults.

FlatTerms are a subset of Terms. -}
data FlatTerm :: * where
  FLet       :: Variable -> FlatTerm -> FlatTerm -> FlatTerm
  FVar       :: Variable -> FlatTerm
  FFix       :: Variable -> FlatTerm -> FlatTerm

  FLit       :: Int -> FlatTerm
  FAdd       :: FlatTerm -> FlatTerm -> FlatTerm

  FConsApp   :: Variable -> [FlatTerm] -> FlatTerm
  FCase      :: FlatTerm               -- ^ Interrogated term
             -> (FlatPattern,FlatTerm) -- ^ Alternative
             -> (Variable,FlatTerm)    -- ^ Default case
             -> FlatTerm
  FCaseEmpty :: FlatTerm -> FlatTerm

  FCocase    :: FlatObsCtx -> FlatTerm -> FlatTerm
  FFun       :: Variable -> FlatTerm -> FlatTerm
  FCoalt     :: (Variable,FlatTerm) -- ^ Destructor Coalternative
             -> FlatTerm            -- ^ Default case
             -> FlatTerm
  FEmpty     :: FlatTerm
  deriving (Eq,Show)

instance Pretty FlatTerm where
  ppInd _ (FLit i)         = show i
  ppInd i (FAdd a b)       = (parens . ppInd i $ a)
                         <+> "+"
                         <+> (parens . ppInd i $ b)
  ppInd _ (FVar s)         = pp s
  ppInd i (FFix s t)       = "fix" <+> pp s <+> "in" <-> indent i (ppInd (i+1) t)
  ppInd i (FLet s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                         <-> indent i ("in" <+> ppInd (i+1) b)
  ppInd i (FConsApp k vs)  = pp k <+> smconcat . fmap (ppInd (i+1)) $ vs
  ppInd i (FCase t (p,u) (y,d)) = ("case" <+> ppInd i t)
                          <-> (indent (i+1) "{" <+> pp p <+> "->"
                               <+> (ppInd (i+2) u))
                          <-> (indent (i+1) "|" <+> pp y <+> "->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd i (FCaseEmpty t) = "case" <+> ppInd i t <+> "{}"
  ppInd i (FCocase c t)    = "cocase" <-> indent (i+1) (ppInd (i+1) c)
                                      <-> indent (i+1) (parens . ppInd (i+1) $ t)

  ppInd i (FFun v t)       =  "{ #" <+> ppInd i v <+> "->"
                          <-> indent (i+1) (ppInd (i+2) t) <+> "}"
  ppInd i (FCoalt (h,u) d) = "{" <+> pp h <+> "# ->"
                               <-> indent (i+1) (ppInd (i+2) u)
                          <-> (indent (i+1) "," <+> "_ ->"
                               <+> (ppInd (i+2) d))
                          <-> (indent (i+1) "}")
  ppInd _ FEmpty           = "{}"

data FlatPattern where
  FlatPatVar  :: Variable -> FlatPattern
  FlatPatCons :: Variable -> [Variable] -> FlatPattern
  deriving (Eq,Show)

instance Pretty FlatPattern where
  pp (FlatPatVar s)     = pp s
  pp (FlatPatCons k vs) = smconcat (pp k:fmap pp vs)

data FlatObsCtx :: * where
  FlatObsFun  :: FlatTerm -> FlatObsCtx
  FlatObsDest :: Variable -> FlatObsCtx
  deriving (Show, Eq)

instance Pretty FlatObsCtx where
  ppInd _ (FlatObsDest h) = brackets (pp h <+> "# ")
  ppInd i (FlatObsFun t)  = "[ #" <+> (parens . ppInd (i+1) $ t) <+> "]"

--------------------------------------------------------------------------------
--                     Flattening Transformation                              --
--------------------------------------------------------------------------------

{- `flattenPattern` will traverse a term, turning (co)case expressions with
   nested (co-)patterns in ones nesting (co)case expressions instead. This
   simplifies translation.

   An example of flattening a case:
   ```
   case (Pair (Pair 0 1) (Pair 1 2))
     { Pair (Pair w x) (Pair y z) -> w + x + y + z }
   ```
   ===>
   ```
   case (Pair 0 (Pair 1 2))
     { Pair p0 p1 ->
         case p0
           { Pair w x ->
               case p1
                { Pair y z -> w + x + y + z
                }
           }
     }
   ```

   An example of flattening a cocase:
   ```
   cocase { Fst # -> 0
          , Fst (Snd #) -> 1
          , Snd (Snd #) -> 2 }
   ```
   ===>
   ```
   cocase { Fst # -> 0
          , Snd # -> cocase { Fst # -> 1
                            , Snd # -> 2 } }
   ```
-}

type FlatM a = State Int a

fresh :: Variable -> FlatM Variable
fresh v = do { n <- get
             ; put (succ n)
             ; return . Variable $ (unVariable v <> show n) }

flattenPgm :: Program Term -> Program FlatTerm
flattenPgm p = Pgm (pgmDecls p)
                   (flatten (pgmConsDestArity p) . pgmTerm $ p)


flatten :: [(Variable,Int)] -> Term -> FlatTerm
flatten w t = fst . runState (flatten' w t) $ 0

flatten' :: [(Variable,Int)] -> Term -> FlatM FlatTerm
flatten' w (Ann t _)     = flatten' w t
flatten' w (Prompt t)    = flatten' w t
flatten' w (App a b)     = FCocase <$> (FlatObsFun <$> flatten' w b)
                                   <*> flatten' w a
flatten' w (Let v a b)   = FLet v <$> flatten' w a <*> flatten' w b
flatten' _ (Lit i)       = return (FLit i)
flatten' w (Add a b)     = FAdd <$> flatten' w a <*> flatten' w b
flatten' _ (Var v)       = return (FVar v)
flatten' w (Fix v t)     = FFix v <$> flatten' w t

{- Eta expand all constructors.

   e.g. K ==> { # x y z -> K x y z } where K has arity 3

  This is done so that we can eliminate the overloaded application nodes. The
  arity for constructors is stored in the map `w`.
-}
flatten' w (Cons k)      =
  case lookup k w of
    Just i  ->
      do { vs <- replicateM i (fresh (Variable "k"))
         ; return (foldr (\v t -> FFun v t) (FConsApp k (fmap FVar vs)) vs) }
    Nothing -> error "flatten' should not happen"

flatten' w (Case t alts) =
  do { t' <- flatten' w t
     ; flattenAlts t' alts }
  where flattenAlts :: FlatTerm -> [(Pattern,Term)] -> FlatM FlatTerm
        flattenAlts e as =
          case as of
            [] -> return (FCaseEmpty e)
            (PVar v,u):_ -> FLet v e <$> flatten' w u
            (PWild,u):_ ->
              do { v <- fresh (Variable "wild")
                 ; FLet v e <$> flatten' w u }
            (PCons k ps,u):as' ->
              let f :: ([Variable],Term)
                    -> Pattern
                    -> FlatM ([Variable],Term)
                  f (vs,n) (PVar v) =
                    return (v:vs,n)
                  f (vs,n) PWild =
                    do { v <- fresh (Variable "wild")
                       ; return (v:vs,n) }
                  f (vs,n) (PCons k'' ps') =
                    do { x <- fresh (Variable "x")
                       ; (vs',n') <- foldM f ([],n) ps'
                       ; return (x:vs, (Case (Var x) [(PCons k'' (fmap PVar vs'),n')]))
                       }
              in
                do { y <- fresh (Variable "y")
                   ; (vs,u') <- foldM f ([],u) ps
                   ; u'' <- flatten' w u'
                   ; def <- flatten' w (Case (Var y) as')
                   ; return (FCase e (FlatPatCons k vs,u'') (y,def)) }

  --    ; case out of
  --        Nothing -> return FEmpty
  --        Just (alt',def) -> return (FCase t' alt' def)
  --    }
  -- where cata :: Variable
  --            -> [(Pattern, Term)]
  --            -> State Int (Maybe ((FlatPattern,FlatTerm),(Variable, FlatTerm)))
  --       cata _ [] = return Nothing
  --       cata y ((PVar v,u):_) =
  --         do { u' <- flatten' w u
  --            ; return . Just $ ((FlatPatVar v,u'),(y,FEmpty))
  --            }
  --       cata y ((PWild,u):_) = undefined u
  --       cata y ((PCons c ps,u):rest) =
  --         do { y' <- fresh (Variable "y")
  --            ; u' <- flatten' w u
  --            ; out' <- cata y' rest
  --            ; case out' of
  --                Nothing -> return . Just $ ((FlatPatCons c [],u'),(y, FEmpty))
  --                Just (alt'',def') ->
  --                  return . Just $ ((FlatPatCons c [],u')
  --                                  ,(y,FCase (FVar y) alt'' def'))
  --            }

{- Eta expand all destructors.

   H ==> { # x -> cocase (H #) x }

  This is done so that we can eliminate the overloaded application nodes. Arity
  for destructors is stored in map `w`, but will always be 1.
-}
flatten' _ (Dest h) =
  do { x <- fresh (Variable "dx")
     ; return (FFun x (FCocase (FlatObsDest h) (FVar x))) }

flatten' w (Cocase c t) = go (unplugObsCtx c) =<< flatten' w t
  where go (Nothing, ObsHead) e = return e
        go (Nothing, ObsFun ObsHead u) e =
          do { u' <- flatten' w u
             ; return (FCocase (FlatObsFun u') e) }
        go (Nothing, ObsDest h ObsHead) e =
          return (FCocase (FlatObsDest h) e)
        go (Just c', ObsFun _ u) e =
          do { e' <- go (unplugObsCtx c') e
             ; u' <- flatten' w u
             ; return (FCocase (FlatObsFun u') e') }
        go (Just c', ObsDest h _) e =
          do { e' <- go (unplugObsCtx c') e
             ; return (FCocase (FlatObsDest h) e') }
        go x _ = error $ "this should not happen. Flatten ObsCtx" <+> show x

flatten' w (Coalts coalts) =
  case coalts of
    -- ^ R-QHead
    (QHead,u):_ -> flatten' w u

    -- ^ R-QPVar
    (QPat QHead (PVar v),u):_ ->
      do { u' <- flatten' w u
         ; return (FFun v u') }

    -- ^ R-QPat
    (QPat QHead p,u):coalts' ->
      do { v <- fresh (Variable "p")
         ; y <- fresh (Variable "y")
         ; t <- flatten' w (Case (Var v) [(p,u),(PVar y,Coalts coalts')])
         ; return (FFun v t)
         }

    -- ^ R-QDest
    (QDest h QHead,u):coalts' ->
      do { u' <- flatten' w u
         ; coalts'' <- flatten' w (Coalts coalts')
         ; return (FCoalt (h,u') coalts'')
         }

    {- Here we add in a case for what to do when there is only one copattern
     left. Because of our call-by-value translation 'cocase {}' cannot be
     applied. We need to know when this is produced and handle it in an adhoc
     way. -}
    (q,u):[] ->
      case unplugCopattern q of
        (Just rest, QPat QHead p) ->
          do { let u'' = Coalts [(rest,  u)]
             ; flatten' w (Coalts [(QPat QHead p, u'')])
             }
        (Just rest, QDest h QHead) ->
          do { u'' <- flatten' w ( Coalts [(rest,  u) ] )
             ; return (FCoalt (h, u'') FEmpty) }
        x -> error $ "TODO flatten'{" <> show x <> "}"

    -- ^ R-Rec
    (q,u):coalts' ->
      case unplugCopattern q of
        (Just rest, QPat QHead p) ->
          do { v  <- fresh (Variable "coalt")
             ; let u'' = Coalts [(rest,  u),(QHead, App (Var v) (invertPattern p))]
             ; flatten' w (Let v (Coalts coalts') (Coalts [(QPat QHead p, u''),(QHead,Var v)]))
             }
        (Just rest, QDest h QHead) ->
          do { v  <- fresh (Variable "coalt")
             ; coalts'' <- flatten' w (Coalts coalts')
             ; u'' <- flatten' w (Coalts [(rest,  u)
                                         ,(QHead, App (Dest h) (Var v))])
             ; return (FLet v coalts'' (FCoalt (h, u'') (FVar v))) }
        x -> error $ "TODO flatten'{" <> show x <> "}"

    -- ^ R-Empty
    [] -> return FEmpty
