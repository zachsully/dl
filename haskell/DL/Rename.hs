module DL.Rename
  ( renamePgm
  , renameDecl
  , renameTerm
  ) where

import Control.Monad
import Data.Map.Lazy
import DL.Syntax.Top
import DL.Syntax.Term
import DL.Syntax.Variable
import DL.Pretty
import Prelude hiding (lookup)

data RnState
  = RnState
  { suffixes :: [Variable]
  , nmap     :: Map Variable Variable }

initRnState :: RnState
initRnState = RnState (fmap (Variable . show) [(0 :: Integer)..]) empty

data Rn a = Rn { unRn :: RnState -> (RnState,a) }

instance Functor Rn where
  fmap = liftM

instance Applicative Rn where
  pure = return
  (<*>) = ap

instance Monad Rn where
  return x = Rn $ \s -> (s,x)
  (Rn f) >>= g = Rn $ \s ->
    let (s',x) = f s in
      unRn (g x) s'

renameVar :: Variable -> Rn Variable
renameVar v = Rn $ \s ->
  let (x:xs) = suffixes s
      v'     = v <> x
      nmap'  = insert v v' (nmap s) in
    (RnState xs nmap',v')

lookupVar :: Variable -> Rn Variable
lookupVar v = Rn $ \s ->
  case lookup v (nmap s) of
    Just v' -> (s,v')
    Nothing -> error (quotes (pp v) <+> "not in renaming map.")

renamePgm :: Program Term -> Program Term
renamePgm pgm = snd $ unRn (renamePgm' pgm) initRnState

renamePgm' :: Program Term -> Rn (Program Term)
renamePgm' (Pgm ds t) = Pgm <$> mapM renameDecl ds <*> renameTerm t

-- | Just renames introduced constructors and destructors
renameDecl :: Decl -> Rn Decl
renameDecl (Decl (Left (NegTyCons name fs projs)))
  =   Decl . Left . NegTyCons name fs
  <$> mapM renameProjection projs
renameDecl (Decl (Right (PosTyCons name fs injs)))
  =   Decl . Right . PosTyCons name fs
  <$> mapM renameInjection injs

renameProjection :: Projection -> Rn Projection
renameProjection (Proj v ty) = renameVar v >>= \v' -> return (Proj v' ty)

renameInjection :: Injection -> Rn Injection
renameInjection (Inj v ty) = renameVar v >>= \v' -> return (Inj v' ty)


renameTerm :: Term -> Rn Term
renameTerm (Let v a b) = Let <$> renameVar v <*> renameTerm a <*> renameTerm b
renameTerm (Ann a ty) = renameTerm a >>= \a' -> return (Ann a' ty)
renameTerm (Lit i) = return (Lit i)
renameTerm (Add a b) = Add <$> renameTerm a <*> renameTerm b
renameTerm (Var v) = Var <$> lookupVar v
renameTerm (Fix v a) = Fix <$> renameVar v <*> renameTerm a
renameTerm (App a b) = App <$> renameTerm a <*> renameTerm b
renameTerm (Cons k) = Cons <$> lookupVar k
renameTerm (Case a alts) = Case <$> renameTerm a <*> mapM renameAlt alts
renameTerm (Dest h) = Dest <$> lookupVar h
renameTerm (Coalts coalts) = Coalts <$> mapM renameCoalt coalts
renameTerm (Cocase o a) = Cocase <$> renameObsCtx o <*> renameTerm a
renameTerm (Prompt a) = Prompt <$> renameTerm a

renameAlt :: (Pattern,Term) -> Rn (Pattern,Term)
renameAlt (p,t) =
  do { p' <- renamePattern p
     ; t' <- renameTerm t
     ; return (p',t') }

renamePattern :: Pattern -> Rn Pattern
renamePattern PWild = return PWild
renamePattern (PVar v) = PVar <$> renameVar v
renamePattern (PCons v ps) = PCons <$> (lookupVar v) <*> (mapM renamePattern ps)

renameCoalt :: (CoPattern,Term) -> Rn (CoPattern,Term)
renameCoalt (q,t) =
  do { q' <- renameCopattern q
     ; t' <- renameTerm t
     ; return (q',t') }

renameCopattern :: CoPattern -> Rn CoPattern
renameCopattern QHead = return QHead
renameCopattern (QDest h q) = QDest <$> lookupVar h <*> renameCopattern q
renameCopattern (QPat q p) = QPat <$> renameCopattern q <*> renamePattern p
renameCopattern (QVar v q) = QVar <$> renameVar v <*> renameCopattern q
renameCopattern QWild = return QWild

renameObsCtx :: ObsCtx -> Rn ObsCtx
renameObsCtx ObsHead       = return ObsHead
renameObsCtx (ObsFun o t)  = ObsFun <$> renameObsCtx o <*> renameTerm t
renameObsCtx (ObsDest h o) = ObsDest <$> lookupVar h <*> renameObsCtx o
renameObsCtx (ObsCut v o)  = ObsCut <$> lookupVar v <*> renameObsCtx o
