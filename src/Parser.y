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
  'tyint'  { TokInt }
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

-- %left str

-- %left ':'
-- %left '|' ','
-- %right '{' '('
-- %left '}' ')'

-- %left '_' '#' 'in'
-- %right num 'data' 'codata' 'fix' '+' 'case' 'cocase'
-- %right '->'

%%

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

program :: { Program }
program : decls term                  { Program $1 $2 }

decl :: { Decl }
decl : 'codata' tysymbol tyvars '{' projs '}'
            {% do { addSymbols Negative $5
                  ; return (Decl Negative $2 $3 $5) } }

     | 'data' tysymbol tyvars '{' injs '}'
            {% do { addSymbols Positive $5
                  ; return (Decl Positive $2 $3 $5) } }

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

tysymbol :: { TySymbol }
tysymbol : str              {% let sym = TySymbol $1 in
                               addTySymbol sym >> return sym }

tyvar :: { TyVariable }
tyvar : str                 {% (isTySymbol (TySymbol $1)) >>=
                               (\b -> case b of
                                        False -> return (TyVariable $1)
                                        True -> parseError []) }

tyvars :: { [TyVariable] }
tyvars : tyvars tyvar         { $2 : $1 }
       | {- empty -}          { [] }

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

type :: { Type }
type : '(' type ')'                   { $2 }
     | 'tyint'                        { TyInt }
     | tyvar                          { TyVar $1 }
     | type '->' type                 { TyArr $1 $3 }
     | tysymbol types                 { TyCons $1 $2 }

types :: { [Type] }
types : type types                    { $1 : $2 }
      | {- empty -}                   { [] }

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
