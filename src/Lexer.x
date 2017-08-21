{
module Lexer (lexFile, lexContents, Token(..)) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+    ;
  "--".*     ;
  $digit+    { TokLit . read }
  \+         { const TokPlus }
  codata     { const TokCodata }
  data       { const TokData }
  where      { const TokWhere }
  cocase     { const TokCocase }
  case       { const TokCase }
  fix        { const TokFix }
  \#         { const TokHash }
  _          { const TokUnderscore }
  \->        { const TokArr }
  \{         { const TokLBrac }
  \}         { const TokRBrac }
  \(         { const TokLParen }
  \)         { const TokRParen }
  \,         { const TokRBrac }
  \|         { const TokRBrac }
  $alpha+    { TokString }

{
data Token
  = TokLit Int
  | TokPlus
  | TokString String
  | TokCodata
  | TokData
  | TokWhere
  | TokCase
  | TokCocase
  | TokFix
  | TokHash
  | TokUnderscore
  | TokArr
  | TokLBrac
  | TokRBrac
  | TokLParen
  | TokRParen
  | TokComma
  | TokMid
  deriving (Eq,Show)

lexFile :: FilePath -> IO [Token]
lexFile fp = alexScanTokens <$> readFile fp

lexContents :: IO [Token]
lexContents = alexScanTokens <$> getContents
}
