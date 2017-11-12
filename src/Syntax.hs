{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Syntax where

import Control.Monad.State
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe
import qualified SimpleSMT as SMT

f $$$ args = return $ SMT.List (SMT.Atom f : args)

iff a b = (a `SMT.implies` b) `SMT.and` (b `SMT.implies` a)

data Expr
  = Var String
  | Union Expr
          Expr
  | Intersect Expr
              Expr
  | Neg Expr
  | FunApp String
           [Expr]
  deriving (Eq, Ord, Show, Read)

data Constr
  = Sub Expr
        Expr
  | NotSub Expr
           Expr
  deriving (Eq, Ord, Show, Read)

subExpressions :: Expr -> [Expr]
subExpressions e = e : concatMap subExpressions (children e)
  where
    children (Var v) = []
    children (Union x y) = [x, y]
    children (Intersect x y) = [x, y]
    children (Neg x) = [x]
    children (FunApp f es) = es

type SubExprs = [Expr]

constrSubExprs :: [Constr] -> SubExprs
constrSubExprs clist = List.nub subExprs
  where
    sides (Sub x y) = [x, y]
    sides (NotSub x y) = [x, y]
    subExprs = [esub | c <- clist, e <- sides c, esub <- subExpressions e]

allExprNums :: SubExprs -> Map.Map Expr Integer
allExprNums elist = Map.fromList $ zip elist [0 ..]

maxArity :: [Expr] -> Int
maxArity es = List.maximum $ (0 :) $ Maybe.catMaybes $ List.map getArity es
  where
    getArity (FunApp f x) = Just $ length x
    getArity _ = Nothing

-- type SBVec = SMT.BitVec
data PredNumConfig = Config
  { predNums :: Map.Map Expr Integer
  , arities :: Map.Map String Int
  , universalVars :: [SMT.SExpr]
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
  let xi = SMT.extract x (toInteger i) (toInteger i)
  "bitToBool" $$$ [xi]

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

clauseForExpr :: Expr -> ConfigM [SMT.SExpr]
clauseForExpr e =
  case e of
    Var _ -> return []
    Neg e2 -> do
      x <- forallVar
      pe <- p e x
      pe2 <- p e2 x
      return [pe `iff` (SMT.bvNot pe2)]
    Union a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return [pe `iff` (pa `SMT.or` pb)]
    Intersect a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return [pe `iff` (pa `SMT.and` pb)]
    FunApp f args -> do
      xs <- forallVars (length args)
      fxs <- f $$$ xs
      lhs <- p e fxs
      rhs <- forM (zip args xs) $ \(ex, x) -> p ex x
      let eqCond = [lhs `iff` (foldr SMT.and (SMT.bool True) rhs)]
      --Need constraint that no g(...) is in f(...) set
      gs <- differentFuns f
      neqConds <-
        forM gs $ \(g, ar) -> do
          xs <- forallVars ar
          gxs <- g $$$ xs
          lhs <- p e gxs
          return (lhs `iff` SMT.bool False)
      return $ eqCond ++ neqConds

initialState vars exprs =
  Config
  {predNums = allExprNums exprs, arities = Map.empty, universalVars = vars}

withNForalls ::
     [SMT.SExpr]
  -> Integer
  -> ([SMT.SExpr] -> ConfigM SMT.SExpr)
  -> ConfigM SMT.SExpr
withNForalls vars numBits comp = do
  result <- comp vars
  return $ SMT.List $ [SMT.Atom "forall", SMT.List (varTypes), result]
  where
    varTypes = map (\x -> SMT.List [x, SMT.tBits numBits]) vars

--TODO include constraint stuff
makePred :: SMT.Solver -> [Constr] -> IO ()
makePred s clist = do
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      numForall = max 1 $ maxArity subExprs
      constrNums = allExprNums subExprs
      vars = map (\i -> SMT.Atom $ "x_univ_" ++ show i) [1 .. numForall]
  SMT.defineFun s "bitToBool" [("b", SMT.tBits 1)] SMT.tBool $
    (SMT.bvBin 1 1 `SMT.bvULeq` SMT.Atom "b")
  let comp =
        withNForalls vars (toInteger $ length subExprs) $ \vars -> do
          clauses <- concat <$> forM subExprs clauseForExpr
          return $ foldr SMT.and (SMT.bool True) clauses
      exprPreds = (flip evalState) (initialState vars subExprs) comp
  SMT.assert s exprPreds
