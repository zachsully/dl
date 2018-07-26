{-# LANGUAGE GADTs, DataKinds, KindSignatures #-}
module DL.Syntax.Top
  ( Program (..)
  , pgmConsDestArity
  , pgmDecls, pgmTerm

  , Decl (..), Polarity (..)
  , mkDataDecl, mkCodataDecl
  , declArity

  , NegativeTyCons (..)
  , Projection (..)
  , negTyArity

  , PositiveTyCons (..)
  , Injection (..)
  , posTyArity
  ) where

import Control.Arrow ((&&&),(<<<))
import Data.Monoid
import DL.Pretty
import DL.Syntax.Type
import DL.Syntax.Variable

--------------------------------------------------------------------------------
--                             Top Level                                      --
--------------------------------------------------------------------------------

data Program :: * -> * where
  Pgm :: [Decl] -> t -> Program t
  deriving Show

pgmConsDestArity :: Program t -> [(Variable,Int)]
pgmConsDestArity pgm =
  concatMap (\(Decl d) ->
               case d of
                 Left n  -> fmap (projName &&& const 1) (projections n)
                 Right n -> fmap (injName &&& (arity <<< injType))
                                 (injections n)
            )
            (pgmDecls pgm)

pgmDecls :: Program t -> [Decl]
pgmDecls (Pgm x _) = x

pgmTerm :: Program t -> t
pgmTerm (Pgm _ x) = x

instance Pretty t => Pretty (Program t) where
  pp pgm = (stringmconcat "\n\n" . fmap pp . pgmDecls $ pgm)
        <> "\n\n"
        <> (pp . pgmTerm $ pgm)

newtype Decl = Decl (Either NegativeTyCons PositiveTyCons)
  deriving Show

mkDataDecl :: PositiveTyCons -> Decl
mkDataDecl   = Decl . Right

mkCodataDecl :: NegativeTyCons -> Decl
mkCodataDecl = Decl . Left


instance Pretty Decl where
  pp (Decl (Left x))  = pp x
  pp (Decl (Right x)) = pp x

declArity :: Decl -> Int
declArity (Decl (Left d))  = length . negTyFVars $ d
declArity (Decl (Right d)) = length . posTyFVars $ d

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
  deriving Show

instance Pretty NegativeTyCons where
  pp tc = "codata" <+> pp (negTyName tc)

negTyArity :: NegativeTyCons -> Int
negTyArity = length . negTyFVars

data Projection
  = Proj
  { projName :: Variable
  , projType  :: Type }
  deriving (Eq,Show)

data PositiveTyCons
  = PosTyCons
  { posTyName  :: Variable
  , posTyFVars :: [Variable]
  , injections :: [Injection]  }
  deriving Show

instance Pretty PositiveTyCons where
  pp tc = "data" <+> pp (posTyName tc)

posTyArity :: PositiveTyCons -> Int
posTyArity = length . posTyFVars

data Injection
  = Inj
  { injName :: Variable
  , injType  :: Type }
  deriving Show
  {- the domain is a maybe value because unary constructors do not take
     arguments, e.g. () : Unit -}
