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

-- pattern Sup :: Expr -> Expr -> Constr
-- pattern Sup x y = Sub y x
sup x y = Sub y x

subExpressions :: Expr -> [Expr]
subExpressions e = e : concatMap subExpressions (children e)
  where
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
  | CAnd CExpr
         CExpr
  | COr CExpr
        CExpr
  | CXor CExpr
         CExpr
  | CImplies CExpr
             CExpr
  | CIff CExpr
         CExpr

--Get the literals in a constraint expression
literalsInCExpr :: CExpr -> Set.Set (Expr, Expr)
literalsInCExpr (CSubset e1 e2) = Set.singleton (e1, e2)
literalsInCExpr (CNot c) = literalsInCExpr c
literalsInCExpr (CAnd c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2
literalsInCExpr (COr c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2
literalsInCExpr (CXor c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2
literalsInCExpr (CImplies c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2
literalsInCExpr (CIff c1 c2) =
  (literalsInCExpr c1) `Set.union` literalsInCExpr c2
