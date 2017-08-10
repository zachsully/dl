module Translation where

import Data.Char (toLower)

import AST

translate :: Src CoDataDcl Observation -> Src RecordDcl RecordIntro
translate = \src ->
  case src of
    SrcDcl     dcl -> SrcDcl (translateDcl dcl)
    SrcIntro intro -> SrcIntro (translateIntro intro)
    SrcExpr    exp -> SrcExpr exp
    s1 :*: s2      -> translate s1 :*: translate s2


translateDcl :: CoDataDcl -> RecordDcl
translateDcl (CoData name vars copats) =
  Record name vars (fmap (\(CoPattern n ty) -> Proj (fmap toLower n) ty) copats)

translateIntro :: Observation -> RecordIntro
translateIntro (Obs coalts) =
  RecordIntro undefined undefined
