module Andersen
  ( parseBansheeString
  ) where

import Control.Applicative ((<|>), many)
import Control.Monad (forM, void)
import Data.Char (isDigit, isLetter)
import Data.Either (rights)
import qualified Data.List as List
import qualified Data.Map as Map
import Syntax
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
  | AFunApp String
            [AExpr]
  deriving (Eq, Ord, Show)

projections :: AExpr -> [AExpr]
projections (AUnion e1 e2) = projections e1 ++ projections e2
projections (AInter e1 e2) = projections e1 ++ projections e2
projections (AFunApp _ args) = concatMap projections args
projections e1@(AProj _ _ e2) = e1 : (projections e2)
projections _ = []

findArities :: AExpr -> [(String, Int)]
findArities (AUnion e1 e2) = findArities e1 ++ findArities e2
findArities (AInter e1 e2) = findArities e1 ++ findArities e2
findArities (AFunApp fstr args) =
  (fstr, length args) : concatMap findArities args
findArities e1@(AProj _ _ e2) = (findArities e2)
findArities _ = []

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
  return $ AFunApp fun args

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

parseBansheeString :: String -> CExpr
parseBansheeString input = toCExpr $ rights $ map parseConstr $ lines input

toCExpr :: [AConstr] -> CExpr
toCExpr constrs = CAnd $ map (singleToCExpr arityMap) constrs
  where
    arityMap =
      Map.fromList $
      concatMap findArities [e | (e1, e2) <- constrs, e <- [e1, e2]]

singleToCExpr :: Map.Map String Int -> AConstr -> CExpr
singleToCExpr arityMap (e1, e2) = helper allProjs Map.empty
  where
    allProjs = List.nub $ concatMap projections [e1, e2]
    helper [] projMap = CSubset (toSetExpr projMap e1) (toSetExpr projMap e2)
    helper (proj@(AProj funName argNum expr):rest) projMap =
      withProjection
        "__freshVarName" --TODO make this unique
        (arityMap Map.! funName)
        (Projection funName argNum (toSetExpr projMap expr))
        (\projExp -> helper rest $ Map.insert proj projExp projMap)
    toSetExpr projMap e =
      case e of
        AUnion e1 e2 -> (self e1) `Union` (self e2)
        AInter e1 e2 -> (self e1) `Intersect` (self e2)
        Zero -> Bottom
        One -> Top
        AVar s -> Var s
        AFunApp nm exprs -> FunApp nm $ map self exprs
        e@(AProj _ _ _) -> projMap Map.! e
      where
        self = toSetExpr projMap

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
