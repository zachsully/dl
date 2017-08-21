{
module Parser where

import Lexer
import DualSyn
}

%name parseProgram Program
%name parseType Type
%name parseTerm Term
%tokentype { Token }
%error { parseError }
%monad { State [Symbol] }

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
  ':'    { TokColon }

%%

Program : decls Term { Program $1 $2 }
        | Term { Program [] $1 }

Type : str { case $1 of
               "Int" -> TyInt
               _ -> parseError [] }
     | str { TyVar (TyVariable $1) }
     | Type Type  { TyApp $1 $2 }
     | Type arr Type { TyFun $1 $3 }
     | '(' Type ')' { $2 }

Decl : codata str strs '{' projs '}' { Decl Negative
       	      	       	   	       	    (TySymbol $2)
					    (map TyVariable $3)
					    $5 }
     | data str strs '{' injs '}'    { Decl Positive
       	      	       	   	       	    (TySymbol $2)
					    (map TyVariable $3)
					    $5 }

decls : Decl         { [$1] }
      | decls Decl   { $2 : $1 }

datad : str ':' Type {% get >>=
                	(\s -> put ((Symbol $1):s))
			>> return (Data (Symbol $1) $3) }

projs : datad           { [$1] }
      | projs ',' datad { $3 : $1 }

injs : datad          { [$1] }
     | injs '|' datad { $3 : $1 }

strs : str        { [$1] }
     | strs str   { $2 : $1 }

Term : num                        { Lit $1 }
     | '(' Term ')'               { $2 }
     | fix str arr Term           { Fix (Variable $2) $4 }
     | case Term '{' alts '}'     { Case $2 $4 }
     | cocase '{' coalts '}'      { CoCase $3 }
     | symbol terms               { Cons $1 $2 }
     | symbol Term                { Dest $1 $2 }
     | var                        { Var $1 }
     | Term '+' Term              { Add $1 $3 }
     | Term Term                  { App $1 $2 }

symbol : str {% get >>=
                (\s -> case elem (Symbol $1) s of
                         True -> return (Symbol $1)
                         False -> parseError [$1]) }

var : str {% get >>=
             (\s -> case not (elem (Symbol $1) s) of
                      True -> return (Variable $1)
                      False -> parseError [$1]) }

terms : Term { [$1] }
      | terms Term { $2 : $1 }

alts : alt { [$1] }
     | alts '|' alt { $3 : $1 }

alt : Pattern arr Term { ($1,$3) }

coalts : coalt { [$1] }
       | coalts ',' coalt { $3 : $1 }

coalt : CoPattern arr Term { ($1,$3) }

Pattern : '_' { PWild }
	| var { PVar $1 }
	| symbol patterns { PCons $1 $2 }

patterns : Pattern { [$1] }
	 | patterns Pattern { $2 : $1 }

CoPattern : '#' { QHash }
	  | symbol CoPattern { QDest $1 $2 }
	  | CoPattern Pattern { QPat $1 $2 }
	  | '(' CoPattern ')' { $2 }

{
data State s a = State { runState :: s -> (s,a) }

instance Functor (State s) where
  fmap f  m = State $ \s -> let (s',a) = (runState m) s in (s',f a)

instance Applicative (State s) where
  pure = return
  a <*> b = undefined

instance Monad (State s) where
  return a = State $ \s -> (s,a)
  m >>= k = State $ \s -> let (s',a) = runState m s
                          in runState (k a) s'

get :: State s s
get = State $ \s -> (s,s)

put :: s -> State s ()
put s = State $ \_ -> (s,())

parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
