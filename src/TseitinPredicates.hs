module TseitinPredicates where

import SMTHelpers
import qualified SimpleSMT as SMT
import Syntax

import Control.Monad.State
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe

import SMTHelpers

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

-- type SBVec = SMT.BitVec
data PredNumConfig = Config
  { predNums :: Map.Map Expr Integer
  , arities :: Map.Map String Int
  , universalVars :: [SMT.SExpr]
  , existentialVars :: [String]
  }

getNumPreds :: ConfigM Int
getNumPreds = (Map.size . predNums) <$> get

type ConfigM = State PredNumConfig

arity :: String -> ConfigM Int
arity f = ((Map.! f) . arities) <$> get

p :: Expr -> SMT.SExpr -> ConfigM SMT.SExpr
p e x = do
  n <- getNumPreds
  i <- ((Map.! e) . predNums) <$> get
    -- let xi = SMT.extract x (toInteger i) (toInteger i)
  return $ ithBit i x n

ithBit i x n = (SMT.not $ (x `SMT.bvAnd` mask) `SMT.eq` SMT.bvBin n 0)
  where
    mask = SMT.bvBin n $ 2 ^ i

forallVar :: ConfigM SMT.SExpr
forallVar = do
  vars <- (universalVars) <$> get
  return $
    case vars of
      [] -> error "No Forall vars"
      h:_ -> h

forallVars :: Int -> ConfigM [SMT.SExpr]
forallVars n = (take n . universalVars) <$> get

differentFuns :: String -> ConfigM [(String, Int)]
differentFuns f = do
  arMap <- arities <$> get
  return $ filter (\(g, _) -> g /= f) $ Map.toList arMap

clauseForExpr :: Expr -> ConfigM SMT.SExpr
clauseForExpr e =
  case e of
    Var _ -> return $ SMT.bool True
    Neg e2 -> do
      x <- forallVar
      pe <- p e x
      pe2 <- p e2 x
      return $ pe <==> (SMT.bvNot pe2)
    Union a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe <==> (pa \/ pb)
    Intersect a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe <==> (pa /\ pb)
    FunApp f args -> do
      xs <- forallVars (length args)
      fxs <- f $$$ xs
      lhs <- p e fxs
      rhs <- forM (zip args xs) $ \(ex, x) -> p ex x
      let eqCond = lhs <==> (andAll rhs)
        --Need constraint that no g(...) is in f(...) set
      gs <- differentFuns f
      neqConds <-
        forM gs $ \(g, ar) -> do
          xs <- forallVars ar
          gxs <- g $$$ xs
          lhs <- p e gxs
          return (lhs <==> SMT.bool False)
      return $ eqCond /\ andAll neqConds
    Top -> do
      x <- forallVar
      px <- p e x
      return px
    Bottom -> do
      x <- forallVar
      px <- p e x
      return $ SMT.not px

constrClause :: Constr -> ConfigM SMT.SExpr
constrClause (e1 `Sub` e2) = do
  x <- forallVar
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 ==> pe2
constrClause (e1 `NotSub` e2) = do
  x <- fresh
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 /\ (SMT.not pe2)

funClause :: (String, Int) -> ConfigM SMT.SExpr
funClause (f, arity) = do
  xs <- forallVars arity
  fxs <- (f $$$ xs)
  "domain" $$$ [fxs]

initialState vars exprs =
  Config
  { predNums = allExprNums exprs
  , arities = getArities exprs
  , universalVars = vars
  , existentialVars = []
  }

fresh :: ConfigM SMT.SExpr
fresh = do
  state <- get
  let oldVars = existentialVars state
      takenVars = Set.fromList oldVars
      varNames = map (\i -> "x_exists_" ++ show i) [1 ..]
      validVars = filter (\x -> not $ x `Set.member` takenVars) varNames
      newVar = head validVars
      newState = state {existentialVars = newVar : oldVars}
  put newState
  return $ SMT.Atom newVar
