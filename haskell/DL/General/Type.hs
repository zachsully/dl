module DL.General.Type where

import Data.Set hiding (foldl)

import DL.General.Variable
import DL.Utils.Pretty
import DL.Utils.StdMonad

--------------------------------------------------------------------------------
--                                  Kind                                      --
--------------------------------------------------------------------------------

newtype Kind = Kind Int
  deriving Eq

instance Pretty Kind where
  pp (Kind 0) = "*"
  pp (Kind n) = "* =>" <+> pp (Kind (n-1))

--------------------------------------------------------------------------------
--                               Type Scheme                                  --
--------------------------------------------------------------------------------

data Scheme = Forall (Set Variable) Constraint Type

instance Pretty Scheme where
  pp (Forall vs c t) = "forall" <+> (smconcat . fmap pp . toList $ vs) <> "."
    <-> indent 2 (ppInd 2 c) <-> (indent 2 ("=>" <+> ppInd 2 t))

instance FV Scheme where
  fvs (Forall vs _ ty) = fvs ty \\ vs

--------------------------------------------------------------------------------
--                               Contraint                                    --
--------------------------------------------------------------------------------

data Constraint
  = CTrue
  | CConj Constraint Constraint
  | CEq Type Type
  | CNumeric Type
  deriving (Eq,Show)

atomicConstr :: Constraint -> Bool
atomicConstr CTrue = True
atomicConstr (CConj _ _) = True
atomicConstr _ = False

instance Pretty Constraint where
  ppInd _ CTrue  = "true"
  ppInd _ (CEq a b) = pp a <+> "=" <+> pp b
  ppInd i (CConj a b) = ppInd i a <-> (indent i (ppInd i b))
  ppInd _ (CNumeric t) = "numeric" <+> (pp t)

instance Semigroup Constraint where
  (<>) = mappend

instance Monoid Constraint where
  mempty = CTrue

  mappend CTrue CTrue = CTrue
  mappend CTrue c     = c
  mappend c     CTrue = c
  mappend a     b     = CConj a b

instance FV Constraint where
  fvs CTrue = empty
  fvs (CConj a b) = union (fvs a) (fvs b)
  fvs (CNumeric a) = fvs a
  fvs (CEq a b) = union (fvs a) (fvs b)

ceq :: Type -> Type -> Constraint
ceq  = CEq

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

data Type
  = TyInt
  | TyArr Type Type
  | TyVar Variable
  | TyCons Variable
  | TyApp Type Type
  deriving (Eq,Show)

atomicTy :: Type -> Bool
atomicTy (TyArr _ _) = False
atomicTy (TyApp _ _) = False
atomicTy _ = True

instance Pretty Type where
  pp TyInt = "Int"
  pp (TyArr a b) =   (parensIf (not . atomicTy) a . pp $ a)
                 <+> "->"
                 <+> (pp b)
  pp (TyVar v) = unVariable v
  pp (TyCons k) = unVariable k
  pp (TyApp a b) = pp a <+> (parensIf (not . atomicTy) b . pp $ b)

instance FV Type where
  fvs TyInt = empty
  fvs (TyArr a b) = fvs a `union` fvs b
  fvs (TyVar v) = singleton v
  fvs (TyCons _) = empty
  fvs (TyApp a b) = fvs a `union` fvs b

arity :: Type -> Int
arity (TyArr _ b) = 1 + arity b
arity _ = 0

domain :: Type -> Maybe Type
domain (TyArr a _) = Just a
domain _ = Nothing

codomain :: Type -> Maybe Type
codomain (TyArr _ b) = Just (codomain' b)
  where codomain' (TyArr _ y) = codomain' y
        codomain' x = x
codomain _ = Nothing

collectTyArgs :: Type -> Maybe (Variable,[Type])
collectTyArgs (TyApp e t) = collectTyArgs e >>= \(k,ts) -> return (k,t:ts)
collectTyArgs (TyCons k)  = return (k,[])
collectTyArgs _           = Nothing

distributeTyArgs :: (Variable,[Type]) -> Type
distributeTyArgs (k,ts) = foldl TyApp (TyCons k) ts
