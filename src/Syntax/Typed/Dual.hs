{-# LANGUAGE GADTs,
             DataKinds,
             RankNTypes #-}
module Syntax.Typed.Dual where

-- import Debug.Trace
-- import Control.Monad.State
-- import Data.Monoid ((<>))

-- import Syntax.Typed.Kind
-- import Syntax.Typed.Type
-- import Syntax.Variable
-- import Utils


--------------------------------------------------------------------------------
--                             Top Level                                      --
--------------------------------------------------------------------------------

-- data Program t
--   = Pgm
--   { pgmDecls :: [Decl]
--   , pgmTerm  :: t }

-- instance Pretty t => Pretty (Program k t) where
--   pp pgm = (stringmconcat "\n\n" . fmap pp . pgmDecls $ pgm)
--         <> "\n\n"
--         <> (pp . pgmTerm $ pgm)

-- flattenPgm :: forall k . Program k Term -> Program k FlatTerm
-- flattenPgm pgm = Pgm (pgmDecls pgm) (flatten . pgmTerm $ pgm)

-- type Decl k = Either (NegativeTyCons k) (PositiveTyCons k)

-- instance (Pretty a,Pretty b) => Pretty (Either a b) where
--   pp _ = ""

-- declArity :: forall k . Decl k -> Int
-- declArity (Left d)  = length . negTyFVars $ d
-- declArity (Right d) = length . posTyFVars $ d

-- {- There is a special polarity type because positive and negative types are
--    declared with the same structure, but we still need to keep them separate. -}
-- data Polarity = Positive | Negative
--   deriving (Eq,Show)
