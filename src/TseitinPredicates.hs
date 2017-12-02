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
  , funVals :: Map.Map String VecFun
  , universalVars :: [BitVector]
  , existentialVars :: [String]
  }

getNumPreds :: ConfigM Int
getNumPreds = (Map.size . predNums) <$> get

type ConfigM = State PredNumConfig

getAllFunctions :: ConfigM [VecFun]
getAllFunctions = (Map.elems . funVals) <$> get

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
  funMap <- funVals <$> get
  return [(g, arity g) | g <- Map.elems funMap, vecFunName g /= vecFunName f]

funNamed :: String -> ConfigM VecFun
funNamed f = do
  funs <- funVals <$> get
  return $ funs Map.! f

functionDomainClause :: Expr -> ConfigM SMT.SExpr
functionDomainClause e = do
  n <- getNumPreds
  case e of
    FunApp fname args -> do
      f <- funNamed fname
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
      return $ pe === (SMT.not pe2)
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

posConstrClause :: BitVector -> Constr -> ConfigM SMT.SExpr
posConstrClause x (e1 `Sub` e2) = do
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 ==> pe2

negConstrClause :: Integral i => i -> Constr -> ConfigM SMT.SExpr
negConstrClause numPreds (e1 `NotSub` e2) = do
  x <- fresh numPreds
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ pe1 /\ (SMT.not pe2)

--Assert that the given function is closed over the domain
funClause :: VecFun -> ConfigM SMT.SExpr
funClause f = do
  n <- getNumPreds
  xs <- forallVars $ arity f
  let fxs = bvApply n f xs
  return $ domain $$$ [fxs]

initialState numBits vars exprs =
  Config
  { predNums = allExprNums exprs
  , funVals =
      Map.fromList
        [ (f, VecFun f (replicate ar [0 .. numBits - 1]))
        | (f, ar) <- Map.toList $ getArities exprs
        ]
  , universalVars = vars
  , existentialVars = []
  }

fresh :: Integral i => i -> ConfigM BitVector
fresh numPreds = do
  state <- get
  n <- getNumPreds
  let oldVars = existentialVars state
      takenVars = Set.fromList oldVars
      varNames = map (\i -> "x_exists_" ++ show i) [0 ..]
      validVars = filter (\x -> not $ x `Set.member` takenVars) varNames
      newVar = head validVars
      newState = state {existentialVars = newVar : oldVars}
  put newState
  return $ nameToBits numPreds newVar
