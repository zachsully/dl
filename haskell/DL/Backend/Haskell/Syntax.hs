module DL.Backend.Haskell.Syntax where

import DL.Syntax.Variable
import DL.Pretty

data HsProgram
  = HsPgm
  { hsPgmDecls :: [HsDecl]
  , hsPgmTerm  :: HsTerm }
  deriving (Show,Eq)

instance Pretty HsProgram where
  pp pgm =   "{-# LANGUAGE GADTs, RankNTypes #-}"
         <-> "module Main where"
         <-> ""
         <-> "import Prelude (Show, IO, error, print, (+),Int,Num)"
         <-> ""
         <-> (vmconcat . fmap pp . hsPgmDecls $ pgm)
         <-> ""
         <-> "prog =" <-> (indent 2 . ppInd 2 . hsPgmTerm $ pgm)
         <-> ""
         <-> "main :: IO ()\nmain = print prog"

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

-- | For GADTs
data HsConstraint
  = HsCEq HsType HsType
  | HsCNumeric HsType
  deriving (Eq,Show)

instance Pretty HsConstraint where
  pp (HsCEq t1 t2) = pp t1 <+> "~" <+> pp t2
  pp (HsCNumeric ty) = "Num" <+> pp ty

-- | The notable difference between Type and HsType is that we have RankNTypes
-- because of HsTyForall
data HsType
  = HsTyInt
  | HsTyArr HsType HsType
  | HsTyVar Variable
  | HsTyCons Variable
  | HsTyApp HsType HsType
  | HsTyForall [Variable] [HsConstraint] HsType
  deriving (Eq,Show)

instance Pretty HsType where
  pp HsTyInt = "Int"
  pp (HsTyArr a b) = ppAtomic a <+> "->" <+> ppAtomic b
  pp (HsTyVar s) = pp s
  pp (HsTyCons s) = pp s
  pp (HsTyApp a b) = ppAtomic a <+> ppAtomic b
  pp (HsTyForall [] [] ty) = pp ty
  pp (HsTyForall [] cs ty)
    = (parens . stringmconcat "," . fmap pp $ cs) <+> "=>" <+> pp ty
  pp (HsTyForall vs cs ty)
    = ("forall"
        <+> (smconcat (fmap pp vs)) <> "."
        <+> (parens . stringmconcat "," . fmap pp $ cs)
        <+> "=>" <+> pp ty)

instance Atomic HsType where
  isAtomic HsTyInt = True
  isAtomic (HsTyVar _) = True
  isAtomic (HsTyCons _) = True
  isAtomic _ = False

-- | Top level declarations
data HsDecl
  = HsDataDecl HsData
  | HsRecordDecl HsRecord
  | HsFunDecl HsFun
  deriving (Eq,Show)

instance Pretty HsDecl where
  pp (HsDataDecl d) = pp d
  pp (HsRecordDecl d) = pp d
  pp (HsFunDecl d) = pp d

-- | Declare a data type
data HsData
  = HsData
  { hsDataName  :: Variable
  , hsDataFVars :: [Variable]
  , hsDataCons  :: [HsDataCon] }
  deriving (Eq,Show)

instance Pretty HsData where
  pp d | hsDataCons d == [] = "data"
                              <+> pp (hsDataName d)
                              <+> (smconcat . fmap unVariable . hsDataFVars $ d)
       | otherwise = "data"
                     <+> pp (hsDataName d)
                     <+> (smconcat . fmap unVariable . hsDataFVars $ d)
                     <+> "where"
                     <-> (vmconcat . fmap pp . hsDataCons $ d)
                     <-> (indent 1 "deriving Show\n")

data HsDataCon
  = HsDataCon
  { hsConName :: Variable
  , hsConType :: HsType }
  deriving (Eq,Show)

instance Pretty HsDataCon where
  pp dc = indent 1 (   pp (hsConName dc)
                   <+> "::"
                   <+> pp . hsConType $ dc )

data HsRecord
  = HsRecord
  { hsRecordName   :: Variable
  , hsRecordFVars  :: [Variable]
  , hsRecordFields :: [HsField] }
  deriving (Eq,Show)

instance Pretty HsRecord where
  pp r = "data"
         <+> pp (hsRecordName r)
         <+> (smconcat . fmap pp . hsRecordFVars $ r)
         <-> indent 1 "="
         <+> pp (hsRecordName r)
         <-> indent 1 "{" <+> (stringmconcat (indent 1 ", ")
                                (fmap pp . hsRecordFields $ r))
         <> indent 1 "} deriving Show"

data HsField
  = HsField
  { hsFieldName        :: Variable
  , hsFieldConstraints :: [HsConstraint]
  , hsFieldType        :: HsType }
  deriving (Eq,Show)

instance Pretty HsField where
  pp f = pp (hsFieldName f)
         <+> "::"
         <>  (case hsFieldConstraints f of
                []     -> mempty
                (c:cs) -> " " <> parens (stringmconcat "," (fmap pp (c:cs))) <+> "=>"
             )
         <+> (ppAtomic . hsFieldType $ f) <> "\n"

-- | Top level function declarations, not these can have type annotations
data HsFun
  = HsFun
  { hsFunName :: Variable
  , hsFunArgs :: [Variable]
  , hsFunType :: Maybe HsType
  , hsFunRhs  :: HsTerm }
  deriving (Eq,Show)

instance Pretty HsFun where
  pp fd =   (case hsFunType fd of
               Nothing -> mempty
               Just ty ->
                 (pp . hsFunName $ fd) <+> "::" <+> pp ty <> "\n")
        <>  (pp . hsFunName $ fd)
        <+> (smconcat . fmap (allLower . unVariable) . hsFunArgs $ fd)
        <+> "="
        <-> indent 2 (ppInd 2 (hsFunRhs fd))

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------
{- This is mostly the same as DualSyn. A lambda term has been introduced to be
   used as an application. The destructor and cocase terms are not present. The
   `fix` term is actually a let
-}

data HsTerm
  = HsLet Variable HsTerm HsTerm
  | HsLit Int
  | HsAdd HsTerm HsTerm
  | HsVar Variable
  | HsLam Variable HsTerm
  | HsApp HsTerm HsTerm
  | HsCons Variable
  | HsCase HsTerm [(HsPattern,HsTerm)]
  | HsFail
  deriving (Eq,Show)

{- `distributeArgs` will take a constructor and its arguments and construct a
   term applying the constructor to all of its arguments -}
distributeArgs :: (Variable,[HsTerm]) -> HsTerm
distributeArgs (k,ts) = foldl HsApp (HsCons k) ts

{- The Int passed in is the indentation level and precedence -}
instance Pretty HsTerm where
  ppInd i (HsLet s a b)
    = (smconcat ["let {",pp s,"="])
      <-> indent (i+1) (ppInd (i+1) a) <+> "}"
      <-> indent i "in"
      <-> indent (i+1) (ppInd (i+1) b)
  ppInd _ (HsLit n) = show n
  ppInd i (HsAdd a b) = ppAtomicInd i a <+> "+" <+> ppAtomicInd i b
  ppInd _ (HsVar s) = pp s
  ppInd i (HsLam s t)
    = parens ( "\\" <> pp s <+> "->" <+> (ppInd (i+3) t))
  ppInd i (HsApp a b) = ppAtomicInd i a <+> ppAtomicInd i b
  ppInd _ (HsCons s) = pp s
  ppInd i (HsCase t alts) =
    "case" <+> ppInd (i+5) t <+> "of"
    <-> (vmconcat . map (indent (i+4) . ppAlt) $ alts)
    where ppAlt (pat,t') = pp pat <+> "->"
                           <-> indent (i+6) (ppInd (i+6) t')
  ppInd _ HsFail = "(error \"match fail\")"

instance Atomic HsTerm where
  isAtomic (HsLit _) = True
  isAtomic (HsVar _) = True
  isAtomic (HsCons _) = True
  isAtomic HsFail = True
  isAtomic _ = False

{- Only need flat patterns here -}
data HsPattern
  = HsPWild
  | HsPVar Variable
  | HsPCons Variable [Variable]
  deriving (Eq,Show)

instance Pretty HsPattern where
  pp HsPWild = "_"
  pp (HsPVar s) = pp s
  pp (HsPCons s vs) = pp s <+> smconcat . fmap pp $ vs



--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------
