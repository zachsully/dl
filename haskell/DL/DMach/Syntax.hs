module DL.DMach.Syntax where

import Data.Set
import DL.General.Variable
import DL.Utils.Pretty
import DL.Utils.FreeVars

{- Note [On the design of the Dual machine language]

In order to have a representation of codata that minimizes jumps at runtime, we
need to represent them as products of computations. This differs from the
intermediate language which represents them as a single matching branch followed
by a fall through case. If we were to use that as our maching representation we
would have loads of unneccessary branching at runtime.
-}

data DMach  :: * where
  DMFix     :: Variable -> DMach -> DMach
  DMLet     :: Variable -- ^ place to store new object
            -> DMach    -- ^ allocatable thing
            -> DMach    -- ^ expression
            -> DMach
  DMObs     :: Variable       -- ^ Closure we're observing
            -> DMObsSort
            -> [Variable]     -- ^ Args
            -> DMach
  DMClosure :: Set Variable   -- ^ Free variables
            -> DMClosSort     -- ^ Observations of codata or function
            -> DMach
  DMConsApp :: Variable       -- ^ Constructor name
            -> [Variable]     -- ^ Args
            -> DMach
  DMLit     :: Int -> DMach
  DMAdd     :: Variable -> Variable -> DMach
  DMFail    :: DMach

instance Pretty DMach where
  pp = undefined

instance FV DMach where
  fvs = undefined

data DMObsSort :: * where
  DMOApp  :: DMObsSort
  DMODest :: Variable -> DMObsSort

instance Pretty DMObsSort where
  pp = undefined

data DMClosSort :: * where
  DMLam    :: [Variable] -> DMach -> DMClosSort
  DMCodata :: [(Variable,DMach)] -> DMClosSort

dmLets :: [(Variable,DMach)] -> DMach -> DMach
dmLets binds a = Prelude.foldr (\(x,y) -> DMLet x y) a binds
