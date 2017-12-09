{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax where

import Control.Monad.State
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

import qualified Data.Graph as Graph

--listInDomain n l = andAll $ map (\i -> "domain" $$ [nthElem l i]) [0 .. n - 1]
data Expr
  = Var String
  | Union Expr
          Expr
  | Intersect Expr
              Expr
  | Neg Expr
  | FunApp String
           [Expr]
  | Top
  | Bottom
  deriving (Eq, Ord, Show, Read)

data Constr
  = Sub Expr
        Expr
  | NotSub Expr
           Expr
  deriving (Eq, Ord, Show, Read)

isPos :: Constr -> Bool
isPos (Sub _ _) = True
isPos (NotSub _ _) = False

--Edges in our expression dependency graph
exprDepEdges :: Expr -> [(Expr, [Expr])]
exprDepEdges e = (e, children e) : concatMap exprDepEdges (children e)

--Find the direct children of the given expression's AST root
children :: Expr -> [Expr]
children (Var v) = []
children (Union x y) = [x, y]
children (Intersect x y) = [x, y]
children (Neg x) = [x]
children (FunApp f es) = es
children Top = []
children Bottom = []

isVar (Var v) = True
isVar _ = False

varName :: Expr -> String
varName (Var v) = v

type SubExprs = [Expr]

constrDepEdges :: [Constr] -> ([Expr], [(Expr, [Expr])])
constrDepEdges clist = (allExprs, mergedPairs)
  where
    sides (Sub x y) = [x, y]
    sides (NotSub x y) = [x, y]
    rawPairs = [edge | c <- clist, e <- sides c, edge <- exprDepEdges e]
    allExprs = List.nub $ map fst rawPairs
    mergedPairs =
      List.nub
        [ ( expr
          , List.nub
              [ subExpr
              | (expr', subExprs) <- rawPairs
              , expr' == expr
              , subExpr <- subExprs
              ])
        | (expr) <- allExprs
        ]

isCycle (Graph.CyclicSCC _) = True
isCycle _ = False

orderedSubExpressions :: [Constr] -> [Expr]
orderedSubExpressions clist =
  if (length topologicalOrder == length allExprs)
    then map ((\(x, _, _) -> x) . unVertex) $ reverse $ topologicalOrder
    else error "Graph is not acyclic"
  where
    (allExprs, pairs) = constrDepEdges clist
    rawExprNums = Map.fromList $ zip allExprs [0 ..]
    exprNum = (rawExprNums Map.!)
    edges = map (\(e, es) -> (e, exprNum e, map exprNum es)) pairs
    (g, unVertex, unKey) = Graph.graphFromEdges edges
    topologicalOrder = Graph.topSort g

allExprNums :: SubExprs -> Map.Map Expr Integer
allExprNums elist = Map.fromList $ zip elist [0 ..]

maxArity :: [Expr] -> Int
maxArity es = List.maximum $ (0 :) $ Maybe.catMaybes $ List.map getArity es
  where
    getArity (FunApp f x) = Just $ length x
    getArity _ = Nothing

getArities :: [Expr] -> Map.Map String Int
getArities exprs = Map.fromList $ Maybe.catMaybes $ map appPair exprs
  where
    appPair (FunApp f l) = Just (f, length l)
    appPair _ = Nothing

constrNot :: Constr -> Constr
constrNot (x `Sub` y) = x `NotSub` y
constrNot (x `NotSub` y) = x `Sub` y

--Arbitrary expressions over constraints
--We only model positive constraints here, since we have allow negation of
--arbitrary boolean expressions
data CExpr
  = CSubset Expr
            Expr
  | CNot CExpr
  | CAnd [CExpr]
  | COr [CExpr]
  | CXor [CExpr]
  | CImplies CExpr
             CExpr
  | CIff CExpr
         CExpr
  deriving (Eq, Ord, Show, Read)

x `sub` y = CSubset x y

x `notsub` y = CNot $ x `sub` y

x `sup` y = CSubset y x

x `notsup` y = y `notsub` x

x `eq` y = CAnd [x `sub` y, y `sub` x]

x `neq` y = COr [x `notsub` y, y `notsub` x]

data Projection = Projection
  { projFun :: String
  , projArgNum :: Int
  , projOf :: Expr
  }

withProjection :: String -> Int -> Projection -> (Expr -> CExpr) -> CExpr
withProjection freshName arity proj f =
  let args =
        map (\i -> Var $ freshName ++ "_projarg" ++ show i) [0 .. arity - 1]
      projVar = args List.!! (projArgNum proj)
      result = f projVar
      --Assert that our expression is equal to the function applied to some fresh variables
      projConstr = (FunApp (projFun proj) args) `eq` (projOf proj)
      --Assert that the variable arguments are empty iff the RHS is empty
      --This is necessary, since F(X1...Xk) is empty if any Xi is empty
      projEqConstrs =
        map
          (\arg -> (CSubset arg Bottom) `CIff` (CSubset (projOf proj) Bottom))
          args
  in CAnd $ [result, projConstr] ++ projEqConstrs

newtype Literal =
  Literal (Expr, Expr)
  deriving (Eq, Ord, Show)

litLhs (Literal (e, _)) = e

litRhs (Literal (_, e)) = e

--Get the literals in a constraint expression
literalsInCExpr :: CExpr -> Set.Set Literal
literalsInCExpr (CSubset e1 e2) = Set.singleton $ Literal (e1, e2)
literalsInCExpr (CNot c) = literalsInCExpr c
literalsInCExpr (CAnd cexprs) = Set.unions $ map literalsInCExpr cexprs
literalsInCExpr (COr cexprs) = Set.unions $ map literalsInCExpr cexprs
literalsInCExpr (CImplies c1 c2) = Set.unions $ map literalsInCExpr [c1, c2]
literalsInCExpr (CXor cexprs) = Set.unions $ map literalsInCExpr cexprs
literalsInCExpr (CIff c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2

--Get the literals in a constraint expression
exprsInCExpr :: CExpr -> Set.Set Expr
exprsInCExpr (CSubset e1 e2) = Set.fromList [e1, e2]
exprsInCExpr (CNot c) = exprsInCExpr c
exprsInCExpr (CAnd cexprs) = Set.unions $ map exprsInCExpr cexprs
exprsInCExpr (COr cexprs) = Set.unions $ map exprsInCExpr cexprs
exprsInCExpr (CXor cexprs) = Set.unions $ map exprsInCExpr cexprs
exprsInCExpr (CImplies c1 c2) = (exprsInCExpr c1) `Set.union` exprsInCExpr c2
exprsInCExpr (CIff c1 c2) = (exprsInCExpr c1) `Set.union` exprsInCExpr c2
