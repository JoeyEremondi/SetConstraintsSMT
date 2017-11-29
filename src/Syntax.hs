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

isPos :: Constr -> Bool
isPos (Sub _ _) = True
isPos (NotSub _ _) = False

-- pattern Sup :: Expr -> Expr -> Constr
-- pattern Sup x y = Sub y x
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
