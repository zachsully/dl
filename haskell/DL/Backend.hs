{-# LANGUAGE ExistentialQuantification #-}
module DL.Backend where

import Control.Monad.State
import Data.Monoid ((<>))

import DL.Syntax.Top
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Pretty

-- | A Backend is an object for which we can apply on operation turning a
-- FlatTerm into a String
data Backend = forall rep. (Pretty rep) => Backend (Program FlatTerm -> rep)

runBackend :: Backend -> Program FlatTerm -> String
runBackend (Backend compile) p = pp (compile p)

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

freshen :: Variable -> TransM Variable
freshen s =
  do { st <- get
     ; put (st { num = succ (num st) })
     ; return (Variable (unVariable s <> show (num st))) }

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
