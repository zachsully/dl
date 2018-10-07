{-# LANGUAGE LambdaCase #-}
module DL.Syntax.Top
  ( Program (..)
  , pgmConsDestArity
  , Metadata (..), Behavior (..)

  , Decl (..), Polarity (..), hasConstraintsDecl

  , NegativeTyCons (..)
  , Projection (..)
  , negTyArity
  , hasConstraintsProj

  , PositiveTyCons (..)
  , Injection (..)
  , posTyArity
  , hasConstraintsInj
  ) where

import Control.Arrow ((&&&),(<<<))
import DL.Pretty
import DL.Syntax.Type
import DL.Syntax.Variable

--------------------------------------------------------------------------------
--                             Top Level                                      --
--------------------------------------------------------------------------------

data Program t
  = Pgm
  { pgmDecls    :: [Decl]
  , pgmTerm     :: t
  , pgmMetadata :: Metadata
  } deriving Show

data Metadata
  = Md
  { mdExpectedBehavior :: Behavior
  } deriving Show

instance Pretty Metadata where
  pp (Md b) = "{- BEHAVIOR:" <+> pp b <+> "-}"

data Behavior
  = ThrowsTypeError
  | ThrowsMatchingError
  | Computes Int
  | Undefined
  deriving (Eq,Show)

instance Pretty Behavior where
  pp ThrowsTypeError     = "TypeError"
  pp ThrowsMatchingError = "MatchingError"
  pp (Computes i)        = show i
  pp Undefined           = "Undefined"

pgmConsDestArity :: Program t -> [(Variable,Int)]
pgmConsDestArity pgm =
  concatMap (\case
                CodataDecl n  -> fmap (projName &&& const 1) (projections n)
                DataDecl n    -> fmap (injName &&& (arity <<< injType))
                                      (injections n)
                IndexDecl _ _ -> []
            )
            (pgmDecls pgm)

instance Pretty t => Pretty (Program t) where
  pp (Pgm [] t md) = pp md <-> pp t
  pp pgm = pp (pgmMetadata pgm) <> newline
        <> (stringmconcat "\n\n" . fmap pp . pgmDecls $ pgm)
        <> "\n\n"
        <> (pp . pgmTerm $ pgm)

data Decl
  = DataDecl   PositiveTyCons
  | CodataDecl NegativeTyCons
  | IndexDecl  Variable [Variable]
  deriving (Show,Eq)

-- | Checks that a declaration does not use type constraints
hasConstraintsDecl :: Decl -> Bool
hasConstraintsDecl (DataDecl d) = or (fmap hasConstraintsInj (injections d))
hasConstraintsDecl (CodataDecl d) =  or (fmap hasConstraintsProj (projections d))
hasConstraintsDecl (IndexDecl _ _) = False

instance Pretty Decl where
  pp (DataDecl x)     = pp x
  pp (CodataDecl x)   = pp x
  pp (IndexDecl n vs) = "index" <+> pp n <+> smconcat (fmap pp vs)

{- There is a special polarity type because positive and negative types are
   declared with the same structure, but we still need to keep them separate. -}
data Polarity = Positive | Negative
  deriving (Eq,Show)

{- Intoduction of positive and negative types are done with NegativeTyCons and
   PositiveTyCons. These two are very similar. The notable difference is in
   projections and injections, where every projection must have domain and a
   codomain, injections may not take arguments. -}
data NegativeTyCons
  = NegTyCons
  { negTyName   :: Variable
  , negTyFVars  :: [Variable]
  , projections :: [Projection] }
  deriving (Show,Eq)

instance Pretty NegativeTyCons where
  pp tc =   "codata" <+> pp (negTyName tc)
        <+> (smconcat (fmap pp (negTyFVars tc)))
        <-> indent 2 "{"
        <+> (stringmconcat "\n  , " (fmap (ppInd 4) (projections tc)))
        <+> "}"

negTyArity :: NegativeTyCons -> Int
negTyArity = length . negTyFVars

data Projection
  = Proj
  { projName        :: Variable
  , projMConstraint :: Maybe Constraint
  , projType        :: Type }
  deriving (Eq,Show)

hasConstraintsProj :: Projection -> Bool
hasConstraintsProj i =
  case projMConstraint i of
    Nothing -> False
    Just _  -> True

instance Pretty Projection where
  ppInd i (Proj n Nothing ty) = pp n <+> ":" <+> ppInd i ty
  ppInd i (Proj n (Just c) ty) = pp n <+> ":" <+> ppInd i c <+> "=>"
    <+> ppInd i ty

data PositiveTyCons
  = PosTyCons
  { posTyName  :: Variable
  , posTyFVars :: [Variable]
  , injections :: [Injection]  }
  deriving (Show,Eq)

instance Pretty PositiveTyCons where
  pp tc =   "data" <+> pp (posTyName tc)
        <+> (smconcat (fmap pp (posTyFVars tc)))
        <-> indent 2 "{"
        <+> (stringmconcat "\n  | " (fmap (ppInd 4) (injections tc)))
        <+> "}"

posTyArity :: PositiveTyCons -> Int
posTyArity = length . posTyFVars

data Injection
  = Inj
  { injName        :: Variable
  , injMConstraint :: Maybe Constraint
  , injType        :: Type }
  deriving (Show,Eq)
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}

hasConstraintsInj :: Injection -> Bool
hasConstraintsInj i =
  case injMConstraint i of
    Nothing -> False
    Just _  -> True

instance Pretty Injection where
  ppInd i (Inj n Nothing ty) = pp n <+> ":" <+> ppInd i ty
  ppInd i (Inj n (Just c) ty) = pp n <+> ":" <+> ppInd i c <+> "=>"
    <+> ppInd i ty
