{
module Parser where

import Control.Monad.State
import Lexer
import DualSyn
}

%name parseProgram program
%name parseType type
%name parseTerm term
%name parseDecl decl
%name parseDatum datad
%tokentype { Token }
%error { parseError }
%monad { State ([TySymbol],[(Symbol,Polarity)]) }

%token
  num      { TokLit $$ }
  '+'      { TokPlus }
  str      { TokString $$ }
  'codata' { TokCodata }
  'data'   { TokData }
  'case'   { TokCase }
  'cocase' { TokCocase }
  'fix'    { TokFix }
  'in'     { TokIn }
  '#'      { TokHash }
  '_'      { TokUnderscore }
  '->'     { TokArr }
  '{'      { TokLBrac }
  '}'      { TokRBrac }
  '('      { TokLParen }
  ')'      { TokRParen }
  ','      { TokComma }
  '|'      { TokMid }
  ':'      { TokColon }

%left str

%left ':'
%left '|' ','
%right '{' '('
%left '}' ')'

%left '_' '#' 'in'
%right num 'data' 'codata' 'fix' '+' 'case' 'cocase'
%right '->'

%%

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

program :: { Program }
program : decls term                  { Program $1 $2 }

decl :: { Decl }
decl : 'codata' str tyvars '{' projs '}'
            {% do { addTySymbol (TySymbol $2)
                  ; addSymbols Negative $5
                  ; return (Decl Negative (TySymbol $2) $3 $5) } }

     | 'data' str tyvars '{' injs '}'
            {% do { addTySymbol (TySymbol $2)
                  ; addSymbols Positive $5
                  ; return (Decl Positive (TySymbol $2) $3 $5) } }

decls :: { [Decl] }
decls : decl decls          { $1 : $2 }
      | {- empty -}         { [] }

datad :: { Data }
datad : str ':' type        { Data (Symbol $1) $3 }

projs :: { [Data] }
projs : projs ',' datad     { $3 : $1 }
      | {- empty-}          { [] }

injs :: { [Data] }
injs : injs '|' datad       { $3 : $1 }
     | {- empty -}          { [] }

tyvars :: { [TyVariable] }
tyvars : tyvars str         { (TyVariable $2) : $1 }
       | {- empty -}        { [] }

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

type :: { Type }
type : '(' type ')'                   { $2 }
     | str
          {% case $1 of
              "Int" -> return TyInt
              _     -> do { b <- isTySymbol (TySymbol $1)
                          ; case b of
                              True -> return (TyCons (TySymbol $1) [])
                              _ -> return (TyVar (TyVariable $1))
                          }
          }
     | type '->' type                 { TyArr $1 $3 }
     | str types                      { TyCons (TySymbol $1) $2 }


types :: { [Type] }
types : types type                    { $2 : $1 }
      | type                          { [$1] }

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------

term :: { Term }
term : num                        { Lit $1 }
     | '(' term ')'               { $2 }
     | 'fix' str 'in' term        { Fix (Variable $2) $4 }
     | 'case' term '{' alts '}'   { Case $2 $4 }
     | 'cocase' '{' coalts '}'    { CoCase $3 }
     | term '+' term              { Add $1 $3 }
     | str terms                  {% getPolarity (Symbol $1) >>= \mp -> return $
                                     case mp of
                                       Nothing -> parseError [TokString $1]
                                       Just Positive -> Cons (Symbol $1) $2
                                       Just Negative -> Dest (Symbol $1) (head $2)
                                  }
     | str                        {% getPolarity (Symbol $1) >>= \mp -> return $
                                     case mp of
                                       Nothing -> Var (Variable $1)
                                       Just _ -> parseError [TokString $1]
                                  }
     | term term                  { App $1 $2 }

terms :: { [Term] }
terms : term                        { [$1] }
      | terms term                  { $2 : $1 }

--------------
-- Matching --
--------------

alt :: { (Pattern,Term) }
alt : pattern '->' term             { ($1,$3) }

alts :: { [(Pattern,Term)] }
alts : alt                          { [$1] }
     | alts '|' alt                 { $3 : $1 }

coalt :: { (CoPattern,Term) }
coalt : copattern '->' term         { ($1,$3) }

coalts :: { [(CoPattern,Term)] }
coalts : coalt                      { [$1] }
       | coalts ',' coalt           { $3 : $1 }

pattern :: { Pattern }
pattern : '_'                       { PWild }
        | str patterns              { PCons (Symbol $1) $2 }
        | str                       { PVar (Variable $1) }

patterns :: { [Pattern] }
patterns : pattern                  { [$1] }
         | patterns pattern         { $2 : $1 }

copattern :: { CoPattern }
copattern : '#'                     { QHash }
          | str copattern           { QDest  (Symbol $1)  $2 }
          | copattern pattern       { QPat $1 $2 }
          | '(' copattern ')'       { $2 }

{
--------------------------------------------------------------------------------
--                                Helpers                                     --
--------------------------------------------------------------------------------

emptyState = ([],[])

addTySymbol :: TySymbol -> State ([TySymbol],ss) ()
addTySymbol s = get >>= \(ts,ss) -> put (s:ts,ss)

isTySymbol :: TySymbol -> State ([TySymbol],ss) Bool
isTySymbol s = elem s . fst <$> get

addSymbols :: Polarity -> [Data] -> State (ts,[(Symbol,Polarity)]) ()
addSymbols p dats = get >>= \(ts,ss) -> put (ts,getSyms dats ++ ss)
  where getSyms = foldr (\(Data sym _) acc -> (sym,p):acc) []

getPolarity :: Symbol -> State (ts,[(Symbol,Polarity)]) (Maybe Polarity)
getPolarity s = get >>= \(_,ss) -> return (lookup s ss)

parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
