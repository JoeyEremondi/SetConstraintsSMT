module TseitinPredicates where

import SMTHelpers
import qualified SimpleSMT as SMT hiding (bvBin, tBits)
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

import Debug.Trace (trace)

domain = Fun "domain"

booleanDomain = Fun "booleanDomain"

funDomain = Fun "functionDomain"

-- type SBVec = SMT.BitVec
data PredNumConfig = Config
  { predNums :: Map.Map Expr Integer
  , arities :: Map.Map VecFun Int
  , universalVars :: [BitVector]
  , existentialVars :: [String]
  }

getNumPreds :: ConfigM Int
getNumPreds = (Map.size . predNums) <$> get

type ConfigM = State PredNumConfig

arity :: VecFun -> ConfigM Int
arity f = ((Map.! f) . arities) <$> get

p :: Expr -> BitVector -> ConfigM SMT.SExpr
p e x = do
  n <- getNumPreds
  i <- ((Map.! e) . predNums) <$> get
    -- let xi = SMT.extract x (toInteger i) (toInteger i)
  return $ ithBit i x n

ithBit i (BitVector x) n = x List.!! (fromInteger i)

forallVar :: ConfigM BitVector
forallVar = do
  [v] <- forallVars 1
  return v

forallVars :: Int -> ConfigM [BitVector]
forallVars n = (take n . universalVars) <$> get

differentFuns :: VecFun -> ConfigM [(VecFun, Int)]
differentFuns f = do
  arMap <- arities <$> get
  return $ filter (\(g, _) -> g /= f) $ Map.toList arMap

functionDomainClause :: Expr -> ConfigM SMT.SExpr
functionDomainClause e = do
  n <- getNumPreds
  case e of
    FunApp f args -> do
      xs <- forallVars (length args)
      let fxs = bvApply n f xs
      lhs <- p e fxs
      rhs <- forM (zip args xs) $ \(ex, x) -> p ex x
        --Need constraint that no g(...) is in f(...) set
      let eqCond = andAll rhs === lhs
      gs <- differentFuns f
      neqConds <-
        forM gs $ \(g, ar) -> do
          xs <- forallVars ar
          let gxs = bvApply n g xs
          lhs <- p e gxs
          return (lhs === SMT.bool False)
      return $ eqCond /\ andAll neqConds
    _ -> return $ SMT.bool True

booleanDomainClause :: BitVector -> Expr -> ConfigM (SMT.SExpr)
booleanDomainClause x e = do
  case e of
    Var _ -> return $ SMT.bool True
    Neg e2 -> do
      pe <- p e x
      pe2 <- p e2 x
      return $ pe === (SMT.bvNot pe2)
    Union a b -> do
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe === (pa \/ pb)
    Intersect a b -> do
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe === (pa /\ pb)
    Top -> do
      px <- p e x
      return px
    Bottom -> do
      px <- p e x
      return $ SMT.not px
    _ -> return $ SMT.bool True

constrClause :: BitVector -> Constr -> ConfigM SMT.SExpr
constrClause x (e1 `Sub` e2) = do
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 ==> pe2
constrClause _ (e1 `NotSub` e2) = do
  x <- fresh
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 /\ (SMT.not pe2)

funClause :: (VecFun, Int) -> ConfigM SMT.SExpr
funClause (f, arity) = do
  n <- getNumPreds
  xs <- forallVars arity
  let fxs = bvApply n f xs
  return $ domain $$ (unwrap fxs)

initialState vars exprs =
  Config
  { predNums = allExprNums exprs
  , arities = getArities exprs
  , universalVars = vars
  , existentialVars = []
  }

fresh :: ConfigM BitVector
fresh = do
  state <- get
  n <- getNumPreds
  let oldVars = existentialVars state
      takenVars = Set.fromList oldVars
      varNames = map (\i -> "x_exists_" ++ show i) [0 ..]
      validVars = filter (\x -> not $ x `Set.member` takenVars) varNames
      newVar = head validVars
      newState = state {existentialVars = newVar : oldVars}
  put newState
  return $ BitVector [SMT.Atom (newVar ++ show i) | i <- [0 .. n - 1]]
