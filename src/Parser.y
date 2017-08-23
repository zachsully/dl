{
module Parser where

import Lexer
import DualSyn
}

%name parseProgram Program
%tokentype { Token }
%error { parseError }

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

%left ':'
%left fix in
%left '}' '('

%right data codata
%right arr
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

Decl : codata str strs '{' projs '}' { Decl Negative
                                            (TySymbol $2)
                                            (map TyVariable $3)
                                            $5 }
     | codata str '{' projs '}' { Decl Negative
                                       (TySymbol $2)
				       []
                                       $4 }
     | data str strs '{' injs '}'    { Decl Positive
                                            (TySymbol $2)
                                            (map TyVariable $3)
                                            $5 }
     | data str '{' injs '}' { Decl Positive
                                    (TySymbol $2)
                                    []
                                    $4 }

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
     | str                        { Var (Variable $1) }
     | str terms                  { Cons (Symbol $1) $2 }
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
parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
