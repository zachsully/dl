{-# LANGUAGE UnicodeSyntax #-}
module AlphaEq where

import Judgement
import VariableSyn
import TypeSyn

αEqVar :: [(Variable,Variable)] → Variable → Variable → Bool
αEqVar [] v w = v == w
αEqVar ((v,w):bound) x y =
  (v == x && w == y) || (v /= x && w /= y && αEqVar bound x y)

αEqType' :: [(Variable,Variable)] → Type → Type → Bool
αEqType' _ TyInt TyInt = True
αEqType' bound (TyArr a b) (TyArr a' b') =
  αEqType' bound a a' && αEqType' bound b b'
αEqType' bound (TyVar v) (TyVar w) = αEqType' bound (TyVar v) (TyVar w)
αEqType' _ (TyCons k) (TyCons j) = k == j
αEqType' bound (TyApp a b) (TyApp a' b') =
  αEqType' bound a a' && αEqType' bound b b'
αEqType' _ _ _ = False

αEqTy :: Type → Type → Bool
αEqTy = αEqType' []

αEqTS' :: [(Variable,Variable)] → TypeScheme → TypeScheme → Bool
αEqTS' bound (TyForall _ τ) (TyForall _ σ) = αEqType' bound τ σ

αEqTS :: TypeScheme → TypeScheme → Bool
αEqTS = αEqTS' []
