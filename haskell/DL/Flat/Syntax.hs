{- |
Module      : DL.Syntax.Flat
Description : Gives the flat core language for the compiler. Provides a
              transformation from the source to core language
-}
module DL.Flat.Syntax
  ( -- * Core flat language
    FlatTerm (..)
  , FlatPattern (..)
  , substFlatTerm
  ) where

import DL.General.Type
import DL.General.Variable
import DL.Utils.Pretty

--------------------------------------------------------------------------------
--                              Flat Terms                                    --
--------------------------------------------------------------------------------
-- | FlatTerms where added because in addition to having only flat (co)patterns,
-- they also have (co)case statements that contain defaults. FlatTerms are a
-- subset of Terms.
data FlatTerm :: * where
  FLet     :: Variable -> FlatTerm -> FlatTerm -> FlatTerm
  FVar     :: Variable -> FlatTerm
  FFix     :: Variable -> FlatTerm -> FlatTerm
  FAnn     :: FlatTerm -> Type -> FlatTerm

  FLit     :: Int -> FlatTerm
  FAdd     :: FlatTerm -> FlatTerm -> FlatTerm

  FConsApp :: Variable -> [FlatTerm] -> FlatTerm
  FCase    :: FlatTerm
           -> (FlatPattern,FlatTerm)
           -> (Variable,FlatTerm)
           -> FlatTerm
    -- ^ Interrogated term -> Alternative -> Default case
  FCaseEmpty :: FlatTerm -> FlatTerm

  FFun       :: Variable -> FlatTerm -> FlatTerm
    -- ^ Copattern match on applicative
  FCoalt     :: (Variable,FlatTerm) -> FlatTerm -> FlatTerm
    -- ^ Destructor coalternative -> default case
  FShift     :: Variable -> FlatTerm -> FlatTerm
    -- ^ Like a shift operation, the variable bould is a covariable
  FEmpty     :: FlatTerm
    -- ^ A failure copattern match
  FPrompt    :: FlatTerm -> FlatTerm

  FObsApp    :: FlatTerm -> FlatTerm -> FlatTerm
  FObsDest   :: Variable -> FlatTerm -> FlatTerm
  FObsCut    :: Variable -> FlatTerm -> FlatTerm

  FStreamCoiter :: (Variable,FlatTerm)
                -> (Variable,FlatTerm) -> FlatTerm -> FlatTerm
  deriving (Eq,Show)



substFlatTerm :: Variable -> FlatTerm -> FlatTerm -> FlatTerm
substFlatTerm v t (FLet v' t0 t1) =
  let t0' = if v == v' then t0 else substFlatTerm v t t0
      t1' = substFlatTerm v t t1 in
    FLet v' t0' t1'
substFlatTerm v t (FVar v') = if v == v' then t else FVar v'
substFlatTerm v t (FFix v' t0) = FFix v' (if v == v' then t0 else substFlatTerm v t t0)
substFlatTerm v t (FAnn t0 ty) = FAnn (substFlatTerm v t t0) ty
substFlatTerm _ _ (FLit i) = FLit i
substFlatTerm v t (FAdd t0 t1) = FAdd (substFlatTerm v t t0) (substFlatTerm v t t1)
substFlatTerm v t (FConsApp k args) = FConsApp k (fmap (substFlatTerm v t) args)
substFlatTerm v t (FCase arg (FlatPatVar v0,t0) (v1,t1))
  = FCase (substFlatTerm v t arg)
          (FlatPatVar v0, if v == v0 then t0 else substFlatTerm v t t0)
          (v1, if v == v1 then t1 else substFlatTerm v t t1)
substFlatTerm v t (FCase arg (FlatPatCons k vs,t0) (v1,t1))
  = FCase (substFlatTerm v t arg)
          (FlatPatCons k vs, if elem v vs then t0 else substFlatTerm v t t0)
          (v1, if v == v1 then t1 else substFlatTerm v t t1)
substFlatTerm v t (FCaseEmpty t0) = FCaseEmpty (substFlatTerm v t t0)
substFlatTerm v t (FFun v' t0) = FFun v' (if v == v' then t0 else substFlatTerm v t t0)
substFlatTerm v t (FCoalt (h,t0) t1) = FCoalt (h, substFlatTerm v t t0) (substFlatTerm v t t1)
substFlatTerm v t (FShift v' t0) = FShift v' (if v == v' then t0 else substFlatTerm v t t0)
substFlatTerm _ _ FEmpty = FEmpty
substFlatTerm v t (FPrompt t0) = FPrompt (substFlatTerm v t t0)
substFlatTerm v t (FObsApp t0 t1) = FObsApp (substFlatTerm v t t0) (substFlatTerm v t t1)
substFlatTerm v t (FObsDest h t0) = FObsDest h (substFlatTerm v t t0)
substFlatTerm v t (FObsCut k t0) = FObsCut k (substFlatTerm v t t0)
substFlatTerm v t (FStreamCoiter (x,a) (y,b) c)
  = FStreamCoiter (x,if (v == x) then a else substFlatTerm v t a)
                  (y,if (v == y) then b else substFlatTerm v t b)
                  (substFlatTerm v t c)


instance Pretty FlatTerm where
  ppInd _ (FLit i)         = show i
  ppInd i (FAdd a b)       = (ppAtomicInd i a)
                         <+> "+"
                         <+> (ppAtomicInd i b)
  ppInd _ (FVar s)         = pp s
  ppInd i (FFix s t)       = "fix" <+> pp s <+> "in"
                           <-> indent (i+5) (ppInd (i+5) t)
  ppInd _ (FAnn t ty)      = pp t <+> ":" <+> pp ty
  ppInd i (FLet s a b)     = "let" <+> pp s <+> "=" <+> ppInd (i+1) a
                            <-> indent i ("in" <+> ppInd (i+3) b)
  ppInd _ (FConsApp k [])  = pp k
  ppInd i (FConsApp k vs@(_:_))  = pp k <+> smconcat . fmap (ppInd (i+1)) $ vs
  ppInd i (FCase t (p,u) (y,d)) =
    ("case" <+> ppAtomicInd (i+6) t)
    <-> (indent (i+2) "{" <+> pp p <+> "->"
          <+> (ppInd (i+4) u))
    <-> (indent (i+2) "|" <+> pp y <+> "->"
          <+> (ppInd (i+4) d))
    <-> (indent (i+2) "}")
  ppInd i (FCaseEmpty t) = "case" <+> ppInd (i+5) t <+> "{}"

  ppInd i (FFun v t)       =  "{ #" <+> ppInd i v <+> "->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd i (FCoalt (h,u) d) = "{" <+> pp h <+> "# ->"
                               <-> indent (i+3) (ppInd (i+3) u)
                          <-> (indent (i+3) "," <+> "_ ->"
                               <+> (ppInd (i+3) d))
                          <-> (indent (i+3) "}")
  ppInd i (FShift v t)     =  "{" <+> ppInd i v <+> "# ->"
                          <-> indent (i+5) (ppInd (i+5) t) <+> "}"
  ppInd _ FEmpty           = "{}"
  ppInd i (FPrompt t)      = "#" <+> ppInd (i+2) t

  ppInd i (FObsApp a b)    =
    "cocase" <-> indent (i+2) ("[#" <+> (ppAtomicInd (i+3) a) <> "]")
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (FObsDest h b)    =
    "cocase" <-> indent (i+2) (brackets (pp h <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (FObsCut v b)    =
    "cocase" <-> indent (i+2) (brackets (pp v <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (FStreamCoiter (x,a) (y,b) c)
                          = "coiter { Head # ->" <+> pp x <> "." <+> ppInd (i+1) a
                            <+> "; Tail # ->" <+> pp y <> "." <+> ppInd (i+1) b
                            <+> "} with"
                            <+> ppInd (i+1) c

instance Atomic FlatTerm where
  isAtomic (FLet _ _ _) = False
  isAtomic (FVar _) = True
  isAtomic (FFix _ _) = False
  isAtomic (FAnn _ _) = False
  isAtomic (FLit _) = True
  isAtomic (FAdd _ _) = False
  isAtomic (FConsApp _ []) = True
  isAtomic (FConsApp _ (_:_)) = False
  isAtomic (FCase _ _ _) = False
  isAtomic (FCaseEmpty _) = False
  isAtomic (FFun _ _) = True
  isAtomic (FCoalt _ _) = True
  isAtomic (FShift _ _) = True
  isAtomic FEmpty = True
  isAtomic (FPrompt _) = False
  isAtomic (FObsApp _ _) = False
  isAtomic (FObsDest _ _) = False
  isAtomic (FObsCut _ _) = False
  isAtomic (FStreamCoiter _ _ _) = False

data FlatPattern where
  FlatPatVar  :: Variable -> FlatPattern
  FlatPatCons :: Variable -> [Variable] -> FlatPattern
  deriving (Eq,Show)

instance Pretty FlatPattern where
  pp (FlatPatVar s)     = pp s
  pp (FlatPatCons k vs) = smconcat (pp k:fmap pp vs)

data FlatCopattern
  = FlatQHead
  | FlatQDest Variable
  | FlatQPat FlatPattern

instance Pretty FlatCopattern where
  ppInd _ FlatQHead = "#"
  ppInd _ (FlatQDest h) = pp h <+> "#"
  ppInd _ (FlatQPat p) = "#" <+> pp p
