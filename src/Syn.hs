module Syn where

import Data.Monoid

type Name = String
type Expr = String

-- Top level preprocessor ast
data Src dcl intro
  = SrcDcl dcl
  | SrcIntro intro
  | SrcExpr String   -- ^ Ignore anything that is not a codata declaration
  | (Src dcl intro) :*: (Src dcl intro)

data EvalStrategy
  = CallByNeed  -- ^ uses Haskell syntax
  | CallByValue -- ^ uses Ocaml syntax

-- Types
data Type
  = TyVar Name
  | TyApp Type Type
  | TyArr Type Type

--------------------------------------------------------------------------------
--                               Codata AST                                   --
--------------------------------------------------------------------------------

data CoDataDcl = CoData Name [Name] [CoPattern]
data CoPattern = CoPattern Name Type
data Observation = Obs [CoAlternative]
data CoAlternative = CoAlt [CoPattern] Expr

--------------------------------------------------------------------------------
--                               Record AST                                   --
--------------------------------------------------------------------------------

data RecordDcl = Record Name [Name] [Proj]
data Proj = Proj Name Type
data RecordIntro = RecordIntro Name [Intro]
data Intro = Intro Name Expr

------------
-- Pretty --
------------

(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

smconcat :: [String] -> String
smconcat = foldr (<+>) mempty

ppSrc :: Src RecordDcl RecordIntro -> String
ppSrc = \src ->
  case src of
    SrcDcl   dcl   -> ppRecordDcl dcl
    SrcIntro intro -> ppIntro intro
    SrcExpr  exp   -> exp
    s1 :*: s2      -> ppSrc s1 <> ppSrc s2

ppType :: Type -> String
ppType = \ty ->
  case ty of
    TyVar n       -> n
    TyApp ty0 ty1 -> "(" <> ppType ty0 <+> ppType ty1 <> ")"
    TyArr ty0 ty1 -> ppType ty0 <+> "->" <+> ppType ty1

ppRecordDcl :: RecordDcl -> String
ppRecordDcl (Record n tyvars projs) =
  smconcat ["data",n,smconcat tyvars,"=",n
           ,"\n  {"
           ,pps projs]
  where pps [] = "  }"
        pps (p:[]) = ppProj p <+> "}"
        pps (p:ps) = ppProj p <> "\n  ," <+> (pps ps)

ppProj :: Proj -> String
ppProj (Proj n ty) = n <+> "::" <+> ppType ty

ppIntro :: RecordIntro -> String
ppIntro = undefined
