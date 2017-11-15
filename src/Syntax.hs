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

import qualified Data.Set as Set

($$) :: String -> [SMT.SExpr] -> SMT.SExpr
f $$ [] = (SMT.Atom f)
f $$ args = SMT.List (SMT.Atom f : args)

($$$) :: String -> [SMT.SExpr] -> ConfigM SMT.SExpr
f $$$ [] = return (SMT.Atom f)
f $$$ args = return $ SMT.List (SMT.Atom f : args)

iff a b = (a ==> b) /\ (b ==> a)

--bvEq x y (_ extract 2 2 ) nil ) ) ) ) (and (=> (bitToBool ((_ extract 0 0 ) y_univ_1 ) ) (bitToBool ((_ extract 1 1 ) y_univ_1= (x `SMT.bvULeq` y) /\ (y `SMT.bvULeq` x)
(===) = SMT.eq

(/\) = SMT.and

(\/) = SMT.or

(==>) = SMT.implies

(<==>) = iff

andAll = foldr SMT.and (SMT.bool True)

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
      return [pe <==> (SMT.bvNot pe2)]
    Union a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return [pe <==> (pa \/ pb)]
    Intersect a b -> do
      x <- forallVar
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return [pe <==> (pa /\ pb)]
    FunApp f args -> do
      xs <- forallVars (length args)
      fxs <- f $$$ xs
      lhs <- p e fxs
      rhs <- forM (zip args xs) $ \(ex, x) -> p ex x
      let eqCond = [lhs <==> (andAll rhs)]
      --Need constraint that no g(...) is in f(...) set
      gs <- differentFuns f
      neqConds <-
        forM gs $ \(g, ar) -> do
          xs <- forallVars ar
          gxs <- g $$$ xs
          lhs <- p e gxs
          return (lhs <==> SMT.bool False)
      return $ eqCond ++ neqConds
    Top -> do
      x <- forallVar
      px <- p e x
      return [px]
    Bottom -> do
      x <- forallVar
      px <- p e x
      return [SMT.not px]

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

makePrelude s n = do
  let Just (datatypeCommand, _) =
        SMT.readSExpr
          ("(declare-datatypes () Production (prod String (Seq (_ BitVec " ++
           show n ++ "))))")
  SMT.command s datatypeCommand
  return ()

--Builds up a function so we can iterate through all elements of our domain
enumeratedDomainClauses :: ConfigM SMT.SExpr
enumeratedDomainClauses = do
  [x, y] <- forallVars 2
  let xInDomain = ("domain" $$ [x])
  let xyInDomain = ("domain" $$ [x]) /\ ("domain" $$ [y])
  let yLeqMax = y `SMT.bvULeq` (SMT.Atom "domainMax")
  let pInRange =
        xInDomain ==> (("dindex" $$ [x]) `SMT.bvULeq` (SMT.Atom "domainMax"))
  let pInverse =
        (xInDomain /\ yLeqMax) ==>
        ((("dindex" $$ [x]) === y) <==> ("atIndex" $$ [y] === x))
  -- let pUnique =
  --       (xyInDomain) ==> (("dindex") $$ [x] === ("dindex" $$ [y])) ==>
  --       (x === y)
  let mustInclude = (pInRange /\ pInverse)
  let mustExclude = (yLeqMax) ==> ("domain" $$ ["atIndex" $$ [y]])
  return $ mustInclude /\ mustExclude

declareEnum :: SMT.Solver -> SMT.SExpr -> IO ()
declareEnum s bvType = do
  SMT.declareFun s "dindex" [bvType] bvType
  SMT.declare s "domainMax" bvType
  SMT.declareFun s "atIndex" [bvType] bvType
  --How many productions for ith non-Terminal?
  SMT.declareFun s "numProductionsFor" [bvType] bvType
  --How many non-terminals are produced in the ith production of X?
  --SMT.declareFun s "ithProdForXLength" [bvType, bvType] bvType
  --What is the function symbol of the ith production for x?
  --SMT.declareFun s "ithProdForXSymb" [bvType, bvType] $ bvType -- TODO make string again SMT.Atom "String"
  --Given:
  -- a non-terminal X
  -- an index i (if we're getting the ith production for X)
  -- the index of the jth non-terminal in the production
  -- Returns the jth non-terminal
  --SMT.declareFun s "ithProdForXSeq" [bvType, bvType, bvType] $ "Seq" $$ [bvType]
  --Inverses for those functions
  -- SMT.declareFun
  --   s
  --   "prodIndex" --TODO fix this, should be string
  --   [bvType, bvType, "Seq" $$ [bvType]]
  --   bvType
  return ()

getArities :: [Expr] -> Map.Map String Int
getArities exprs = Map.fromList $ Maybe.catMaybes $ map appPair exprs
  where
    appPair (FunApp f l) = Just (f, length l)
    appPair _ = Nothing

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

validDomain :: ConfigM SMT.SExpr
validDomain = do
  vars <- universalVars <$> get
  varResults <- forM vars (\x -> "domain" $$$ [x])
  return $ andAll varResults

setOptions s = do
  SMT.simpleCommand s ["set-option", ":produce-unsat-cores", "true"]
  return ()

--TODO include constraint stuff
makePred :: SMT.Solver -> [Constr] -> IO (Maybe [(SMT.SExpr, SMT.Value)])
makePred s clist = do
  setOptions s
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      numForall = max 2 $ maxArity subExprs
      constrNums = allExprNums subExprs
      tBitVec = SMT.tBits $ toInteger numPreds
      vars = map (\i -> SMT.Atom $ "y_univ_" ++ show i) [1 .. numForall]
  makePrelude s numPreds
  SMT.defineFun s "bitToBool" [("b", SMT.tBits 1)] SMT.tBool $
    (SMT.bvBin 1 1 `SMT.bvULeq` SMT.Atom "b")
  let comp =
        withNForalls vars (toInteger $ length subExprs) $ \vars -> do
          predClauses <- concat <$> forM subExprs clauseForExpr
          subClauses <- forM clist $ constrClause
          let allClauses = andAll (predClauses ++ subClauses)
          isValidDomain <- validDomain
          funPairs <- (Map.toList . arities) <$> get
          funClauses <- forM funPairs funClause
          let singleFunClause = andAll funClauses
          enumClauses <- enumeratedDomainClauses
          return $
            (isValidDomain ==> allClauses) /\ singleFunClause /\ enumClauses
      (exprPreds, state) = runState comp (initialState vars subExprs)
  --Declare each of our existential variables 
  --Declare our domain function
  SMT.declareFun s "domain" [SMT.tBits $ toInteger numPreds] SMT.tBool
  --Declare functions to get the enumeration of our domain
  declareEnum s tBitVec
  --Delare our constructors
  let funPairs = Map.toList $ arities state
  forM funPairs $ \(f, arity) -> do
    SMT.declareFun s f (replicate arity $ tBitVec) tBitVec
  --Declare our existential variables
  forM (existentialVars state) $ \v -> do
    SMT.declare s v (SMT.tBits $ toInteger numPreds)
    --Assert that each existential variable is in our domain
    SMT.assert s $ "domain" $$ [SMT.Atom v]
  --Assert our domain properties
  SMT.assert s exprPreds
  result <- SMT.check s
  case result of
    SMT.Sat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-model"]
      domainMax <- SMT.getExpr s $ SMT.Atom "domainMax"
      let (SMT.Bits _ maxNum) = domainMax
      forM [0 .. maxNum] $ \i -> do
        result <- SMT.getExpr s $ "atIndex" $$ [SMT.bvBin numPreds i]
        putStrLn (show i ++ " " ++ show result)
      return Nothing --TODO fix
    SMT.Unsat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-unsat-core"]
      return Nothing
    SMT.Unknown -> error "Failed to solve quanitification"
