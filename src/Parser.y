{
module Parser where

import Control.Monad.State
import Lexer
import DualSyn
}

%name parseProgram Program
%tokentype { Token }
%error { parseError }
%monad { State [(Symbol,Polarity)] }

%token
  num    { TokLit $$ }
  '+'    { TokPlus }
  str    { TokString $$ }
  codata { TokCodata }
  data   { TokData }
  case   { TokCase }
  cocase { TokCocase }
  fix    { TokFix }
  in     { TokIn }
  '#'    { TokHash }
  '_'    { TokUnderscore }
  arr    { TokArr }
  '{'    { TokLBrac }
  '}'    { TokRBrac }
  '('    { TokLParen }
  ')'    { TokRParen }
  ','    { TokComma }
  '|'    { TokMid }
  ':'    { TokColon }

%left ':' '_' '#'
%left in
%left '}' '('

%right str num
%right data codata fix arr
%right '+'
%right '|' ',' ':'
%right '{' ')'
%right case cocase

%%

Program : decls Term { Program $1 $2 }
        | Term { Program [] $1 }

Type : str                            { case $1 of
                                          "Int" -> TyInt
                                          _     -> TyVar (TyVariable $1) }
     | '(' Type ')'                   { $2 }
     | str types                      { TyCons (TySymbol $1) $2 }
     | Type arr Type                  { TyArr $1 $3 }

types : Type { [$1] }
      | types Type { $2 : $1 }

Decl : codata str strs '{' projs '}'
         {% addSymbols Negative $5 >>
            return (Decl Negative (TySymbol $2) (map TyVariable $3) $5) }
     | codata str '{' projs '}'
         {% addSymbols Negative $4 >>
            return (Decl Negative (TySymbol $2) [] $4) }
     | data str strs '{' injs '}'
         {% addSymbols Positive $5 >>
            return (Decl Positive (TySymbol $2) (map TyVariable $3) $5) }
     | data str '{' injs '}'
         {% addSymbols Positive $4 >>
            return (Decl Positive (TySymbol $2) [] $4) }

decls : Decl         { [$1] }
      | decls Decl   { $2 : $1 }

datad : str ':' Type { (Data (Symbol $1) $3) }

projs : datad           { [$1] }
      | projs ',' datad { $3 : $1 }

injs : datad          { [$1] }
     | injs '|' datad { $3 : $1 }

strs : str        { [$1] }
     | strs str   { $2 : $1 }

Term : num                        { Lit $1 }
     | '(' Term ')'               { $2 }
     | fix str in Term            { Fix (Variable $2) $4 }
     | case Term '{' alts '}'     { Case $2 $4 }
     | cocase '{' coalts '}'      { CoCase $3 }
     | Term '+' Term              { Add $1 $3 }
     | str terms                  {% get >>= \s -> return $
                                     case lookup (Symbol $1) s of
                                       Nothing -> parseError [TokString $1]
                                       Just Positive -> Cons (Symbol $1) $2
                                       Just Negative -> Dest (Symbol $1) (head $2)
                                  }
     | str                        {% get >>= \s -> return $
                                     case lookup (Symbol $1) s of
                                       Nothing -> Var (Variable $1)
                                       Just _ -> parseError [TokString $1]
                                  }
     | Term Term                  { App $1 $2 }

terms : Term { [$1] }
      | terms Term { $2 : $1 }

alts : alt { [$1] }
     | alts '|' alt { $3 : $1 }

alt : Pattern arr Term { ($1,$3) }

coalts : coalt { [$1] }
       | coalts ',' coalt { $3 : $1 }

coalt : CoPattern arr Term { ($1,$3) }

Pattern : '_' { PWild }
        | str patterns { PCons (Symbol $1) $2 }
        | str { PVar (Variable $1) }

patterns : Pattern { [$1] }
         | patterns Pattern { $2 : $1 }

CoPattern : '#' { QHash }
          | str CoPattern { QDest  (Symbol $1)  $2 }
          | CoPattern Pattern { QPat $1 $2 }
          | '(' CoPattern ')' { $2 }

{
addSymbols :: Polarity -> [Data] -> State [(Symbol,Polarity)] ()
addSymbols p dats = get >>= \s -> put (getSyms dats ++ s)
  where getSyms = foldr (\(Data sym _) acc -> (sym,p):acc) []

parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
