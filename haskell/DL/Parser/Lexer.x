{
module DL.Parser.Lexer
  (lexFile, lexString, lexContents, Token(..)) where

import System.Directory
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+    ;
  "--".*     ;
  "{-"       { const TokPragmaOpen }
  "-}"       { const TokPragmaClose }
  $digit+    { TokLit . read }
  Int        { const TokInt }
  \+         { const TokPlus }
  codata     { const TokCodata }
  data       { const TokData }
  index      { const TokIndex }
  cocase     { const TokCocase }
  coiter     { const TokCoiter }
  with       { const TokWith }
  case       { const TokCase }
  fix        { const TokFix }
  let        { const TokLet }
  letrec     { const TokLet }
  =          { const TokEq }
  in         { const TokIn }
  \#         { const TokHash }
  □         { const TokBox }
  ▪         { const TokBoxFill }
  _          { const TokUnderscore }
  \->        { const TokArr }
  =>         { const TokDArr }
  →         { const TokArr }
  \{         { const TokLBrace }
  \}         { const TokRBrace }
  \(         { const TokLParen }
  \)         { const TokRParen }
  \[         { const TokLBrack }
  \]         { const TokRBrack }
  \,         { const TokComma }
  \.         { const TokPeriod }
  \|         { const TokMid }
  \:         { const TokColon }
  \;         { const TokSemiColon }
  module     { const TokModule }
  $alpha+    { TokString }

{
data Token
  = TokLit Int
  | TokInt
  | TokPlus
  | TokString String
  | TokCodata
  | TokData
  | TokIndex
  | TokCase
  | TokCocase
  | TokCoiter
  | TokWith
  | TokFix
  | TokLet
  | TokLetrec
  | TokEq
  | TokIn
  | TokHash
  | TokBox
  | TokBoxFill
  | TokUnderscore
  | TokArr
  | TokDArr
  | TokLBrace
  | TokRBrace
  | TokLParen
  | TokRParen
  | TokLBrack
  | TokRBrack
  | TokComma
  | TokPeriod
  | TokMid
  | TokColon
  | TokSemiColon
  | TokModule
  | TokPragmaOpen
  | TokPragmaClose
  deriving (Eq,Show)

alexScanTokens' :: String -> Either String [Token]
alexScanTokens' s = go ('\n',[],s)
  where go inp@(_,_,s') =
          case alexScan inp 0 of
            AlexEOF -> Right []
            AlexError e -> Left ( "<lexical error> " ++ show e )
            AlexSkip inp' _ -> go inp'
            AlexToken inp' len act ->
              case go inp' of
                Left e -> Left e
                Right ts -> Right (act (take len s') : ts)

lexFile :: FilePath -> IO (Either String [Token])
lexFile fp =
  do { exists <- doesFileExist fp
     ; case exists of
         False -> return (Left ("file " ++ "'" ++ fp ++ "' does not exist"))
         True  -> alexScanTokens' <$> readFile fp
     }

lexString :: String -> Either String [Token]
lexString = alexScanTokens'

lexContents :: IO (Either String [Token])
lexContents = alexScanTokens' <$> getContents
}
