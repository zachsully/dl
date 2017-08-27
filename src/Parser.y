{
module Parser where

import Control.Monad.State
import Lexer
import DualSyn
}
-- All shift/reduce conflicts
%expect 17

%name parseProgram program
%name parseType type
%name parseTerm term
%tokentype { Token }
%error { parseError }
%monad { State ([TyVariable],[(Variable,Polarity)]) }

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

%%

strs :: { [String] }
strs : strs str                                { $2 : $1 }
     | str                                     { [$1] }

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

program :: { Program }
program : decls term                           { Pgm $1 $2 }

decl :: { Decl }
decl : 'codata' str strs '{' projs '}'         { Left (NegTyCons $2 $3 $5) }
     | 'data'   str strs '{' injs  '}'         { Right (PosTyCons $2 $3 $5) }

decls :: { [Decl] }
decls : decl decls                             { $1 : $2 }
      | {- empty -}                            { [] }

proj :: { Projection }
proj : str ':' type '->' type                  {% do { addVar $1 Negative
                                                     ; return (Proj $1 $3 $5) } }
projs :: { [Projection] }
projs : projs ',' proj                         { $3 : $1 }
      | proj                                   { [$1] }
      | {- empty-}                             { [] }

inj :: { Injection }
inj : str ':' type                             {% do { addVar $1 Positive
                                                     ; return (Inj $1 $3)  } }

injs :: { [Injection] }
injs : injs '|' inj                            { $3 : $1 }
     | inj                                     { [$1] }
     | {- empty -}                             { [] }

--------------------------------------------------------------------------------
--                                 Types                                      --
--------------------------------------------------------------------------------

type :: { Type }
type : type0                           { $1 }

-- try type constructor
type0 :: { Type }
type0 :  type typeA                    { TyApp $1 $2 }
      |  type1                         { $1 }

-- try function
type1 :: { Type }
type1 :  type '->' type                { TyArr $1 $3 }
      |  typeA                         { $1 }

typeA :: { Type }
typeA : '(' type ')'                   { $2 }
      | 'tyint'                        { TyInt }
      | str                            {% do { b <- isTyCons $1
                                             ; return (case b of
                                                         True -> TyCons $1
                                                         False -> TyVar $1)
                                             }
                                       }

--------------------------------------------------------------------------------
--                                 Terms                                      --
--------------------------------------------------------------------------------

term :: { Term }
term : term1                      { $1 }

term1 :: { Term }
term1 :  term  termA              { App $1 $2 }
      |  term2                    { $1 }

term2 :: { Term }
term2 :  termA '+' termA          { Add $1 $3 }
      |  'fix' str 'in' term      { Fix $2 $4 }
      |  'case' term '{' alts '}' { Case $2 $4 }
      |  'cocase' '{' coalts '}'  { CoCase $3 }
      |  termA                    { $1 }

{- We lookup to see if the string is defined as a symbol and a singleton
   constructor, otherwise it is a variable. -}
termA :: { Term }
termA :  num                      { Lit $1 }
      |  str                      {% do { mp <- getPolarity $1
                                        ; case mp of
                                            Nothing -> return (Var $1)
                                            Just Negative -> return (Dest $1)
                                            Just Positive -> return (Cons $1)
                                        }
                                  }
      |  '(' term ')'             { $2 }

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
        | str patterns              { PCons $1 $2 }
        | str                       { PVar $1 }

patterns :: { [Pattern] }
patterns : pattern                  { [$1] }
         | patterns pattern         { $2 : $1 }

copattern :: { CoPattern }
copattern : '#'                     { QHash }
          | str copattern           { QDest $1 $2 }
          | copattern pattern       { QPat $1 $2 }
          | '(' copattern ')'       { $2 }

{
--------------------------------------------------------------------------------
--                                Helpers                                     --
--------------------------------------------------------------------------------

emptyState = ([],[])

addTyCons :: TyVariable -> State ([TyVariable],ss) ()
addTyCons s = get >>= \(ts,ss) -> put (s:ts,ss)

isTyCons :: TyVariable -> State ([TyVariable],ss) Bool
isTyCons s = elem s . fst <$> get

addVar :: Variable -> Polarity -> State (ts,[(Variable,Polarity)]) ()
addVar s p = get >>= \(ts,ss) -> put (ts,(s,p):ss)

getPolarity :: Variable -> State (ts,[(Variable,Polarity)]) (Maybe Polarity)
getPolarity s = get >>= \(_,ss) -> return (lookup s ss)

parseError :: [Token] -> a
parseError ts = error ("parse error: " ++ show ts)
}
