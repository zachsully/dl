module DL.DMach.CodeGen (cCompile) where

import DL.Backend
import DL.Flat.Syntax
import DL.DMach.Syntax
import DL.DMach.Translation (trans)
import DL.Utils.Pretty

data CLike

instance Pretty CLike where
  pp = undefined

cCompile :: Backend FlatTerm
cCompile = Backend (codeGen . trans)

codeGen :: DMach -> CLike
codeGen = undefined
