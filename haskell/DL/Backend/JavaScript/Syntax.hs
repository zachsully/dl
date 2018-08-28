{-# LANGUAGE GADTs #-}

module DL.Backend.JavaScript.Syntax where

import Data.List(foldl',isPrefixOf)

import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Pretty
import DL.Translation hiding (freshen)
import qualified DL.Syntax.Top  as Top
import DL.Utils

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

--------------------------------------------------------------------------------
--                              Translation                                   --
--------------------------------------------------------------------------------

instance Translate Program where
  translate = trans

trans :: Top.Program FlatTerm -> Program
trans dpgm = Pgm (aNorm . transTerm . Top.pgmTerm $ dpgm)

-- Because aNorm and transTerm freshen variables and thus return type Std JSTerm, we must extract the term from the Std Monad
transTerm :: FlatTerm -> JSTerm
transTerm f = 
    case runStd (transTerm' f) of
        Left _ -> error ""
        Right x -> x
       
-- We a-Normalize for sharing       
aNorm :: JSTerm -> JSTerm
aNorm f = 
    case runStd (aNorm' f) of
        Left _ -> error ""
        Right x -> x


aNorm' :: JSTerm -> Std JSTerm
  
aNorm' (JSLet vs ts a) = do ts' <- mapM aNorm' ts
                            a' <- aNorm' a
                            return $ JSLet vs ts' a'  
aNorm' (JSRec v t) = do t' <- aNorm' t
                        return $ JSRec v t'
aNorm' (JSLit i) = return $ JSLit i
aNorm' (JSAdd a b) = do a' <- aNorm' a
                        b' <- aNorm' b
                        return $ JSAdd a' b'
aNorm' (JSVar v) = return $ JSVar v
aNorm' (JSFun v t) = do t' <- aNorm' t
                        return $ JSFun v t'
aNorm' (JSApp a b) = do x <- freshen (Variable "a")
                        a' <- aNorm' a
                        b' <- aNorm' b
                        return $ JSLet [x] [b'] (JSApp a' (JSVar x) ) 
aNorm' (JSObj (v,t) d) = do t' <- aNorm' t
                            d' <- aNorm' d
                            return $ JSObj (v,t') d'
aNorm' (JSMethod v t) = do t' <- aNorm' t
                           return $ JSMethod v t'
aNorm' (JSFail) = return $ JSFail        
        

transTerm' :: FlatTerm -> Std JSTerm

transTerm' (FLet v a b) = do a' <- transTerm' a
                             b' <- transTerm' b
                             return $ JSLet [v] [a'] b'
                             
transTerm' (FVar v) = return $ JSVar v

transTerm' (FFix v a) = do a' <- transTerm' a
                           return $ JSRec v a'
                           
transTerm' (FLit i) = return $ JSLit i

transTerm' (FAdd a b) = do a' <- transTerm' a
                           b' <- transTerm' b
                           return $ JSAdd a' b'
                           
transTerm' (FConsApp v xs) = do vars <- mapM (\x -> freshen (Variable "x")) xs
                                xs' <- mapM transTerm' xs
                                let body = JSFun (Variable "c") (foldl' JSApp (JSMethod v (JSVar (Variable "c"))) (map JSVar vars))
                                return $ JSLet vars xs' body

transTerm' (FCase t ((FlatPatVar p),a) (v,u)) = do t' <- transTerm' t
                                                   a' <- transTerm' a
                                                   u' <- transTerm' u
                                                   -- pass identity function into default case
                                                   let def = JSApp (JSFun (v) u') (JSFun (Variable "x") (JSVar (Variable "x")))
                                                   return $ JSApp t' (JSObj (p,a') def)
                                               
transTerm' (FCase t ((FlatPatCons p ps),a) (v,u)) = do t' <- transTerm' t
                                                       a' <- transTerm' a
                                                       u' <- transTerm' u
                                                       -- pass identity function into default case
                                                       let def = JSApp (JSFun (v) u') (JSFun (Variable "x") (JSVar (Variable "x")))
                                                       return $ JSApp t' (JSObj (p,foldr JSFun a' ps) def)

transTerm' (FCaseEmpty t) = transTerm' t

transTerm' (FCocase (FlatObsDest v) t) = do t' <- transTerm' t
                                            return $ JSMethod v t'
                                            
                                            
transTerm' (FCocase (FlatObsFun a) b) = do a' <- transTerm' a
                                           b' <- transTerm' b
                                           return $ JSApp b' a'
                                           
transTerm' (FFun v t) = do t' <- transTerm' t
                           return $ JSFun v t'
                           
transTerm' (FCoalt (v, t) a) = do t' <- transTerm' t
                                  a' <- transTerm' a
                                  return $ JSObj (v, t') a'
                                  
transTerm' (FEmpty) = return $ JSFail
  
