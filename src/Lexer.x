{
module Lexer (lexFile, lexString, lexContents, Token(..)) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-

  $white+    ;
  "--".*     ;
  $digit+    { TokLit . read }
  Int        { const TokInt }
  \+         { const TokPlus }
  codata     { const TokCodata }
  data       { const TokData }
  cocase     { const TokCocase }
  case       { const TokCase }
  fix        { const TokFix }
  let        { const TokLet }
  =          { const TokEq }
  in         { const TokIn }
  \#         { const TokHash }
  □         { const TokBox }
  ▪         { const TokBoxFill }
  _          { const TokUnderscore }
  \->        { const TokArr }
  →         { const TokArr }
  \{         { const TokLBrace }
  \}         { const TokRBrace }
  \(         { const TokLParen }
  \)         { const TokRParen }
  \[         { const TokLBrack }
  \]         { const TokRBrack }
  \,         { const TokComma }
  \|         { const TokMid }
  \:         { const TokColon }
  $alpha+    { TokString }

{
data Token
  = TokLit Int
  | TokInt
  | TokPlus
  | TokString String
  | TokCodata
  | TokData
  | TokCase
  | TokCocase
  | TokFix
  | TokLet
  | TokEq
  | TokIn
  | TokHash
  | TokBox
  | TokBoxFill
  | TokUnderscore
  | TokArr
  | TokLBrace
  | TokRBrace
  | TokLParen
  | TokRParen
  | TokLBrack
  | TokRBrack
  | TokComma
  | TokMid
  | TokColon
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
lexFile fp = alexScanTokens' <$> readFile fp

lexString :: String -> Either String [Token]
lexString = alexScanTokens'

lexContents :: IO (Either String [Token])
lexContents = alexScanTokens' <$> getContents
}
