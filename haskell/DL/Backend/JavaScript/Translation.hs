module DL.Backend.JavaScript.Translation (jsCompile) where

import DL.Backend
import DL.Backend.JavaScript.Syntax
import qualified DL.Syntax.Top as Top
import Data.List (foldl')
import DL.Syntax.Flat
import DL.Syntax.Variable
import DL.Utils

jsCompile :: Backend
jsCompile = Backend trans

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

transTerm' (FConsApp v xs) = do vars <- mapM (\_ -> freshen (Variable "x")) xs
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

transTerm' (FAnn t _) = transTerm' t
transTerm' (FCocase (FlatObsCut _) _) = error "transTerm'{cut}"
transTerm' (FShift _ _) = error "transTerm'{shift}"
transTerm' (FPrompt t) = transTerm' t
