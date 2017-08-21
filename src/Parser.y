{
module Parser where

import Lexer
import DualSyn
}

%name parse
%tokentype { Token }
%error { parseError }

%token
  num    { TokLit $$ }
  '+'    { TokPlus }
  str    { TokString $$ }
  codata { TokCodata }
  data   { TokData }
  where  { TokWhere }
  case   { TokCase }
  cocase { TokCocase }
  fix    { TokFix }
  '#'    { TokHash }
  '_'    { TokUnderscore }
  arr    { TokArr }
  '{'    { TokLBrac }
  '}'    { TokRBrac }
  '('    { TokLParen }
  ')'    { TokRParen }
  ','    { TokComma }
  '|'    { TokMid }

%%

Program : decls Term { undefined }

Decl : num { undefined }

decls : Decl         { [$1] }
      | decls Decl   { $2 : $1 }

Term : num           { \p -> Lit $1 }
     | '(' Term ')'  { $2 }

Pattern : '_' { PWild }

Copattern : '#' { QHash }

{
parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
