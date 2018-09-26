{-# LANGUAGE GADTs #-}

module DL.Backend.JavaScript.Syntax where

import Data.List (isPrefixOf)
import DL.Pretty
import DL.Syntax.Variable

data Program
  = Pgm
  { pgmTerm     :: JSTerm }
  deriving (Show,Eq)


--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------

data JSTerm where
  JSLet     :: [Variable] -> [JSTerm] -> JSTerm -> JSTerm
  JSRec     :: Variable -> JSTerm -> JSTerm
  JSLit     :: Int -> JSTerm
  JSAdd     :: JSTerm -> JSTerm -> JSTerm
  JSVar     :: Variable -> JSTerm
  JSFun     :: Variable -> JSTerm -> JSTerm
  JSApp     :: JSTerm -> JSTerm -> JSTerm
  JSObj     :: (Variable,JSTerm) -> JSTerm -> JSTerm
  JSMethod  :: Variable -> JSTerm -> JSTerm
  JSFail    :: JSTerm
  deriving (Eq,Show)

--------------------------------------------------------------------------------
--                              Pretty Print                                  --
--------------------------------------------------------------------------------

replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace n r h@(x:xs) = if isPrefixOf n h
                           then r ++ replace n r (drop (length n) h)
                           else x : replace n r xs
replace _ _ [] = []


instance Pretty Program where
  pp pgm =   "appDest = function (v,t){"
         <-> "  if (typeof t[v] === 'function'){"
         <-> "      if (t.isEval){"
         <-> "          return eval(\"t.\" + v +\"()\")"
         <-> "      }else{"
         <-> "          let value = eval(\"t.\" + v +\"()\"); t.isEval = true; t.v = value; return value;"
         <-> "      }"
         <-> "  }else{"
         <-> "      return appDest(v,t._def)"
         <-> "  }}"
         <-> ""
         <-> "var prog =" <-> ((\t -> ppTerm t 1) . pgmTerm $ pgm)
         <-> ""
         <-> "console.log(prog)"

ppTerm :: JSTerm
          -> Int -- Number of indents
          -> String

ppTerm (JSLet vs ts a) i = "function(){" <+> foldr (<+>) "" (zipWith printLet vs ts) <-> indent i "return" <+> parens (ppTerm a (i+1)) <-> indent (i-1) "}()"
                           where printLet v t = "" <-> indent i "let" <+> pp v <+> "=" <+> ppTerm t (i+1) <> ";"
ppTerm (JSRec v a) i = "function" <+> pp v <> "()" <> braces ("return" <+> replace (pp v) (pp v <> "()") (parens (ppTerm a i))) <> "()"
ppTerm (JSLit i) _ = show i
ppTerm (JSAdd a b) i = ppTerm a i <+> "+" <+> ppTerm b i
ppTerm (JSVar v) _ = show v
ppTerm (JSFun v t) i = "function" <+> parens (pp v) <> braces ("return" <+> parens (ppTerm t i))
ppTerm (JSApp a b) i = "" <-> indent i (parens (ppTerm a (i+1))) <-> indent i (parens (ppTerm b (i+1))) <-> indent (i-1) ""
ppTerm (JSObj (v,t) u) i = "{isEval:false," <+> pp v <> ":" <> "function()" <> braces ("return" <+> parens (ppTerm t i)) <> ", _def:" <> ppTerm u i <> "}"
ppTerm (JSMethod v t) i = "appDest(" <> "\"" <> pp v <> "\"" <> "," <> ppTerm t i <> ")"
ppTerm (JSFail) _ = "{}"
