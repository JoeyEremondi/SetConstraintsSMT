module Andersen where

import Control.Applicative ((<|>), many)
import Control.Monad (forM, void)
import Data.Char (isDigit, isLetter)
import Text.Parsec (ParseError, oneOf, parse, sepBy, try)
import Text.Parsec.Char (char, digit, letter, string)
import Text.Parsec.Combinator (many1, notFollowedBy)
import Text.Parsec.String (Parser)

-- import Text.Parsec.String.Char (char, digit, oneOf, satisfy)
-- import Text.Parsec.String.Combinator (chainl1, choice, many1)
-- import Text.Parsec.String.Parsec (try)
data AExpr
  = AUnion AExpr
           AExpr
  | AInter AExpr
           AExpr
  | AProj String
          Int
          AExpr
  | AVar String
  | Zero
  | One
  | FunApp String
           [AExpr]
  deriving (Eq, Ord, Show)

type AConstr = (AExpr, AExpr)

isLeft (Left _) = True
isLeft _ = False

--http://jakewheat.github.io/intro_to_parsing/
lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

integer :: Parser Int
integer = read <$> lexeme (many1 digit)

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

identifier :: Parser String
identifier = lexeme ((:) <$> firstChar <*> many nonFirstChar)
  where
    firstChar = letter <|> char '_'
    nonFirstChar = digit <|> firstChar

zero :: Parser AExpr
zero = do
  void $ string "0"
  return Zero

one :: Parser AExpr
one = do
  void $ string "1"
  return One

funApp :: Parser AExpr
funApp = do
  fun <- identifier
  void $ char '('
  args <- expr `sepBy` (char ',')
  void $ char ')'
  return $ FunApp fun args

var :: Parser AExpr
var = AVar <$> identifier

expr :: Parser AExpr
expr = (try funApp) <|> (try proj) <|> (try zero) <|> (try one) <|> (try var)

proj :: Parser AExpr
proj = do
  fun <- identifier
  void $ char '['
  fun <- identifier
  void $ char ','
  argNum <- integer
  void $ char ','
  e <- expr
  void $ char ']'
  return $ AProj fun argNum e

constr :: Parser AConstr
constr = do
  e1 <- expr
  void $ string "<="
  e2 <- expr
  return (e1, e2)

parseConstr :: String -> Either ParseError AConstr
parseConstr = parse constr ""

parseExpr :: String -> Either ParseError AExpr
parseExpr = parse expr ""

parseFile :: String -> IO [Either ParseError AConstr]
parseFile f = do
  theLines <- lines <$> readFile f
  return $ filter isLeft $ map parseConstr theLines

parseHead f = do
  theLines <- lines <$> readFile f
  return $ parseConstr $ head theLines
