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
import qualified SimpleSMT as SMT

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

($$) :: String -> [SMT.SExpr] -> SMT.SExpr
f $$ [] = (SMT.Atom f)
f $$ args = SMT.List (SMT.Atom f : args)

($$$) :: String -> [SMT.SExpr] -> ConfigM SMT.SExpr
f $$$ [] = return (SMT.Atom f)
f $$$ args = return $ SMT.List (SMT.Atom f : args)

iff a b = (a ==> b) /\ (b ==> a)

(===) = SMT.eq

(/\) = SMT.and

(\/) = SMT.or

(==>) = SMT.implies

(<==>) = iff

--tString = SMT.Atom "String"
--tList t = "List" $$ [t]
andAll l =
  case l of
    [] -> SMT.bool True
    _ -> foldr1 SMT.and $ filter (/= SMT.bool True) l

-- string s = SMT.Atom $ ['"'] ++ s ++ ['"']
-- slCons h t = "insert" $$ [t, h]
-- sList = foldl slCons (SMT.Atom "nil")
-- applyList f n l = f $$ (map (nthElem l) [0 .. n - 1])
-- nthElem :: SMT.SExpr -> Int -> SMT.SExpr
-- nthElem l 0 = "head" $$ [l]
-- nthElem l n = nthElem ("tail" $$ [l]) (n - 1)
sshow s = SMT.showsSExpr s ""

vshow = sshow . SMT.value

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

pattern Sup :: Expr -> Expr -> Constr
pattern Sup x y = Sub y x

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

makePrelude s n funPairs = do
  SMT.defineFun s "bitToBool" [("b", SMT.tBits 1)] SMT.tBool $
    (SMT.bvBin 1 1 `SMT.eq` SMT.Atom "b")
  let bvTypeS = sshow $ SMT.tBits n
  let variants =
        (flip map) funPairs $ \(f, arity) ->
          let symbols =
                List.intercalate " " $
                (flip map) [0 .. arity - 1] $ \i ->
                  " (toSymb_" ++ f ++ "_" ++ show i ++ " " ++ bvTypeS ++ " )"
          in "(prod_" ++ f ++ symbols ++ ")"
  let Just (datatypeCommand, _) =
        SMT.readSExpr
          ("(declare-datatypes () ((Production " ++
           (List.intercalate " " variants) ++ ")))")
  SMT.command s datatypeCommand
  return ()

--Builds up a function so we can iterate through all elements of our domain
--enumeratedDomainClauses :: ConfigM SMT.SExpr
enumeratedDomainClauses funPairs = do
  results <-
    forM funPairs $ \(f, arity) -> do
      (num:fx:vars) <- forallVars $ arity + 2
      let prod = ("prod_" ++ f) $$ vars
      return $
        ("isProduction" $$ [fx, prod]) <==>
        ((fx === (f $$ vars)) /\ ("domain" $$ [fx]) /\
         (andAll $ map (\v -> "domain" $$ [v]) vars))
  --Assert that every x has a production
  --This makes sure our finite domain maps to the Herbrand domain
  x <- forallVar
  let hasProd =
        ("domain" $$ [x]) ==> ("isProduction" $$ [x, "productionFor" $$ [x]])
  return $ (andAll results) /\ hasProd

declareEnum :: SMT.Solver -> SMT.SExpr -> IO ()
declareEnum s bvType = do
  SMT.declareFun s "isProduction" [bvType, SMT.Atom "Production"] SMT.tBool
  SMT.declareFun s "productionFor" [bvType] (SMT.Atom "Production")
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

readValueList :: SMT.Solver -> SMT.SExpr -> IO [SMT.Value]
readValueList s sexp = helper sexp []
  where
    helper sexp accum = do
      lValue <- SMT.getExpr s sexp
      case lValue of
        SMT.Other (SMT.Atom "nil") -> return accum
        _ -> do
          hd <- SMT.getExpr s ("head" $$ [sexp])
          helper ("tail" $$ [sexp]) $ accum ++ [hd]

enumerateDomain :: SMT.Solver -> SMT.SExpr -> IO [SMT.Value]
enumerateDomain s bvType = do
  SMT.simpleCommand s ["push"]
  SMT.declare s ("domain-val") bvType
  SMT.assert s $ "domain" $$ [domainVal]
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    domainVal = SMT.Atom "domain-val"
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          valueExpr <- SMT.getExpr s domainVal
          SMT.assert s (SMT.not ((SMT.value valueExpr) === domainVal))
          helper (valueExpr : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant enumerating domain"

enumerateProductions :: SMT.Solver -> SMT.SExpr -> IO [SMT.Value]
enumerateProductions s fromSymbol = do
  SMT.simpleCommand s ["push"]
  SMT.declare s ("prod-val") $ SMT.Atom "Production"
  SMT.assert s $ "isProduction" $$ [fromSymbol, productionVal]
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    productionVal = SMT.Atom "prod-val"
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          prod <- SMT.getExpr s productionVal
          SMT.assert s (SMT.not ((SMT.value prod) === productionVal))
          helper (prod : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant"

varProductions :: SMT.Solver -> Expr -> Integer -> Int -> IO [SMT.Value]
varProductions s v i n = do
  SMT.simpleCommand s ["push"]
  SMT.declare s vname $ SMT.tBits $ toInteger n
  SMT.assert s $ "domain" $$ [matchingVal]
  SMT.assert s $ ithBit i matchingVal n
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    vname = "varprod-" ++ (filter isAlphaNum (varName v))
    matchingVal = SMT.Atom vname
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          prod <- SMT.getExpr s matchingVal
          SMT.assert s (SMT.not ((SMT.value prod) === matchingVal))
          helper (prod : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant"

--TODO include constratailint stuff
makePred :: SMT.Solver -> [Constr] -> IO (Maybe [(SMT.SExpr, SMT.Value)])
makePred s clist = do
  setOptions s
  SMT.simpleCommand s ["push"]
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      numForall = 2 + maxArity subExprs
      constrNums = allExprNums subExprs
      tBitVec = SMT.tBits $ toInteger numPreds
      vars = map (\i -> SMT.Atom $ "y_univ_" ++ show i) [1 .. numForall]
      state0 = (initialState vars subExprs)
      funPairs = (Map.toList . arities) state0
      allFreeVars :: [Expr] = filter isVar subExprs
  makePrelude s (toInteger numPreds) funPairs
  let comp =
        withNForalls vars (toInteger $ length subExprs) $ \vars -> do
          predClauses <- forM subExprs clauseForExpr
          subClauses <- forM clist $ constrClause
          let allClauses = andAll (predClauses ++ subClauses)
          isValidDomain <- validDomain
          funClauses <- forM funPairs funClause
          let singleFunClause = andAll funClauses
          enumClauses <- enumeratedDomainClauses funPairs
          return $
            (isValidDomain ==> allClauses) /\ singleFunClause /\ enumClauses
      (exprPreds, state) = runState comp state0
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
  --TODO minimize?
  case result of
    SMT.Sat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-model"]
      domain <- enumerateDomain s tBitVec
      putStrLn $ show $ map vshow domain
      forM domain $ \d -> do
        prodsFrom <- enumerateProductions s $ SMT.value d
        forM prodsFrom $ \p -> putStrLn $ vshow d ++ "  ->  " ++ vshow p
      forM allFreeVars $ \v -> do
        prods <- varProductions s v ((predNums state) Map.! v) numPreds
        forM prods $ \prod -> putStrLn $ show v ++ "  ->  " ++ vshow prod
      return Nothing --TODO fix
    SMT.Unsat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-unsat-core"]
      return Nothing
    SMT.Unknown -> error "Failed to solve quanitification"
