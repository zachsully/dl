{
{-# LANGAUGE DataKinds #-}
module Parser where

import Control.Monad
import Data.Monoid

import Lexer
import DualSyn
import VariableSyn
import KindSyn
import TypeSyn
import Utils
}
-- All shift/reduce conflicts
%expect 14

%name parseProgram program
%name parseType type
%name parseTerm term
%tokentype { Token }
%error { pfail }
%monad { ParserM }{ (>>=) }{ return }

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
  'let'    { TokLet }
  '='      { TokEq }
  'in'     { TokIn }
  '#'      { TokHash }
  '□'     { TokBox }
  '▪'     { TokBoxFill }
  '_'      { TokUnderscore }
  '->'     { TokArr }
  '{'      { TokLBrace }
  '}'      { TokRBrace }
  '('      { TokLParen }
  ')'      { TokRParen }
  '['      { TokLBrack }
  ']'      { TokRBrack }
  ','      { TokComma }
  '|'      { TokMid }
  ':'      { TokColon }

%%

strs :: { [String] }
strs : strs str                                { $2 : $1 }
     | str                                     { [$1] }
     | {- empty -}                             { [] }

var :: { Variable }
var : str                                      { Variable $1 }

vars :: { [Variable] }
vars : strs                                    { fmap Variable $1 }

--------------------------------------------------------------------------------
--                              Top Level                                     --
--------------------------------------------------------------------------------

program :: { Program Term }
program : decls term                           { Pgm $1 $2 }

decl :: { Decl }
decl : 'codata' var vars '{' projs '}'         { Left (NegTyCons $2
                                                        (reverse $3)
                                                        (reverse $5)) }
     | 'data'   var vars '{' injs  '}'         { Right (PosTyCons $2
                                                          (reverse $3)
                                                          (reverse $5)) }

decls :: { [Decl] }
decls : decl decls                             { $1 : $2 }
      | {- empty -}                            { [] }

proj :: { Projection }
proj : var ':' type '->' type                  {% do { addVar $1 Negative
                                                     ; return (Proj $1 $3 $5) } }
projs :: { [Projection] }
projs : projs ',' proj                         { $3 : $1 }
      | proj                                   { [$1] }
      | {- empty-}                             { [] }

inj :: { Injection }
inj : var ':' type                             {% do { addVar $1 Positive
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
      | var                            {% do { b <- isTyCons $1
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
term1 :  termA  term              { App $1 $2 }
      |  '▪' termA               { Prompt $2 }
      |  term2                    { $1 }

term2 :: { Term }
term2 :  term '+' termA                { Add $1 $3 }
      |  'cocase' '{' coalts '}'       { CoCase (reverse $3) }
      |  'fix' var 'in' term           { Fix $2 $4 }
      |  'let' var '=' term 'in' term  { Let $2 $4 $6 }
      |  'case' term '{' alts '}'      { Case $2 (reverse $4) }
      |  termA                         { $1 }

{- We lookup to see if the string is defined as a symbol and a singleton
   constructor, otherwise it is a variable. -}
termA :: { Term }
termA :  num                      { Lit $1 }
      |  var                      {% do { mp <- getPolarity $1
                                        ; case mp of
                                            Nothing -> return (Var $1)
                                            Just Negative -> return (Dest $1)
                                            Just Positive -> return (Cons $1)
                                        }
                                  }
      | '(' term ')'              { $2 }
      | '{' coalts '}'                 { CoCase (reverse $2) }


--------------
-- Matching --
--------------

alt :: { (Pattern,Term) }
alt : pattern '->' term          { ($1,$3) }

alts :: { [(Pattern,Term)] }
alts : alt                       { [$1] }
     | alts '|' alt              { $3 : $1 }
     | {- empty -}               { [] }

coalt :: { (CoPattern,Term) }
coalt : copattern '->' term      { ($1,$3) }

coalts :: { [(CoPattern,Term)] }
coalts : coalt                   { [$1] }
       | coalts ',' coalt        { $3 : $1 }
       | {- empty -}             { [] }

pattern :: { Pattern }
pattern : var patterns           { PCons $1 (reverse $2) }
        | var                    { PCons $1 [] }

patternA :: { Pattern }
patternA : '_'                   { PWild }
         | var                   { PVar $1 }
         | '(' pattern ')'       { $2 }

patterns :: { [Pattern] }
patterns : patternA              { [$1] }
         | patterns patternA     { $2 : $1 }

copattern :: { CoPattern }
copattern : copattern patternA   { QPat $1 $2 }
          | copattern0           { $1 }

copattern0 :: { CoPattern }
copattern0 : var copatternA      {% do { mp <- getPolarity $1
                                       ; case mp of
                                           Nothing -> return (QVar $1 $2)
                                           Just Negative -> return (QDest $1 $2)
                                           Just Positive ->
                                             error ("constructor" <+> pp $1 <+>
                                                    " in copattern.")
                                       }
                                 }
           | copatternA          { $1 }

copatternA :: { CoPattern }
copatternA : '#'                    { QHead }
           | '□'                   { QHead }
           | '[' copattern ']'      { $2 }

{
--------------------------------------------------------------------------------
--                                Helpers                                     --
--------------------------------------------------------------------------------

data ParserM a
  = ParserM
  { runParserM :: ([Variable],[(Variable,Polarity)])
               -> Either String (a,([Variable],[(Variable,Polarity)]))
  }

instance Functor ParserM where
  fmap f m = ParserM $ \s ->
    case runParserM m s of
      Left e -> Left e
      Right (a,s') -> Right (f a, s')

instance Applicative ParserM where
  pure = return
  (<*>) = ap

instance Monad ParserM where
  return x = ParserM $ \s -> Right (x,s)
  m >>= f = ParserM $ \s ->
    case runParserM m s of
      Left e -> Left e
      Right (x,s') -> runParserM (f x) s'

get :: ParserM ([Variable],[(Variable,Polarity)])
get = ParserM $ \s -> Right (s,s)

put :: ([Variable],[(Variable,Polarity)]) -> ParserM ()
put s = ParserM $ \_ -> Right ((),s)

emptyState = ([],[])

addTyCons :: Variable -> ParserM ()
addTyCons s = get >>= \(ts,ss) -> put (s:ts,ss)

isTyCons :: Variable -> ParserM Bool
isTyCons s = elem s . fst <$> get

addVar :: Variable -> Polarity -> ParserM ()
addVar s p = get >>= \(ts,ss) -> put (ts,(s,p):ss)

getPolarity :: Variable -> ParserM (Maybe Polarity)
getPolarity s = get >>= \(_,ss) -> return (lookup s ss)

pfail :: [Token] -> ParserM a
pfail ts = ParserM $ \_ -> Left ("<parse error>: " ++ show ts)
}
