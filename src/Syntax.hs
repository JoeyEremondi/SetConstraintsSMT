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

orderedSubExpressions :: [Constr] -> [Expr]
orderedSubExpressions clist =
  map ((\(x, _, _) -> x) . unVertex) $ reverse $ Graph.topSort g
  where
    (allExprs, pairs) = constrDepEdges clist
    rawExprNums = Map.fromList $ zip allExprs [0 ..]
    exprNum = (rawExprNums Map.!)
    edges = map (\(e, es) -> (e, exprNum e, map exprNum es)) pairs
    (g, unVertex, unKey) = Graph.graphFromEdges edges

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

x `sub` y = CSubset x y

x `notsub` y = CNot $ x `sub` y

x `sup` y = CSubset y x

x `notsup` y = y `notsub` x

x `eq` y = CAnd [x `sub` y, y `sub` x]

x `neq` y = COr [x `notsub` y, y `notsub` x]

--Get the literals in a constraint expression
literalsInCExpr :: CExpr -> Set.Set (Expr, Expr)
literalsInCExpr (CSubset e1 e2) = Set.singleton (e1, e2)
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
