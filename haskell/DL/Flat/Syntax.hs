{- |
Module      : DL.Syntax.Flat
Description : Gives the flat core language for the compiler. Provides a
              transformation from the source to core language
-}
module DL.Flat.Syntax
  ( -- * Core flat language
    FlatTerm (..)
  , FlatPattern (..)
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
  deriving (Eq,Show)

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
    "cocase" <-> ("[#" <+> (ppAtomicInd (i+3) a) <> "]")
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (FObsDest h b)    =
    "cocase" <-> (brackets (pp h <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)
  ppInd i (FObsCut v b)    =
    "cocase" <-> (brackets (pp v <+> "#"))
             <-> indent (i+2) (ppAtomicInd (i+2) b)

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
