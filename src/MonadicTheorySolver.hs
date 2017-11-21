{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module MonadicTheorySolver where

import SMTHelpers
import qualified SimpleSMT as SMT
import Syntax
import TseitinPredicates

import Control.Monad.State
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe
import qualified SimpleSMT as SMT

import SMTHelpers
import TreeGrammar

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

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

--Clauses asserting that our production checking function is correct
--and asserting that each value in our domain is reachable through some production
enumeratedDomainClauses funPairs = do
  results <-
    forM funPairs $ \(f, arity) -> do
      (num:fx:vars) <- forallVars $ arity + 2
      return $
        ((isFProduction f) $$ (fx : vars)) ===
        ((fx === (f $$ vars)) /\ ("domain" $$ [fx]) /\
         (andAll $ map (\v -> "domain" $$ [v]) vars))
  --Assert that every x has a production
  --This makes sure our finite domain maps to the Herbrand domain
  x <- forallVar
  --We or each of these conditions
  let hasProdConds =
        (flip map) funPairs $ \(f, arity) -> do
          ("domain" $$ [x]) ==>
            ((isFProduction f) $$
             (x : [productionFor i $$ [x] | i <- [0 .. arity - 1]]))
  return $ (andAll results) /\ (orAll hasProdConds)

isFProduction f = "isProductionFor-" ++ f

productionFor i = "productionFor" ++ show i

declareEnum :: SMT.Solver -> SMT.SExpr -> [(String, Int)] -> Int -> IO ()
declareEnum s bvType funPairs maxArity = do
  forM funPairs $ \(f, arity) -> do
    SMT.declareFun
      s
      (isFProduction f)
      (bvType : replicate arity bvType)
      SMT.tBool
  forM [0 .. maxArity - 1] $ \argNum -> do
    SMT.declareFun s (productionFor argNum) [bvType] bvType
  return ()

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
  return ()
  --SMT.simpleCommand s ["set-option", ":produce-unsat-cores", "true"]
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

enumerateProductions ::
     SMT.Solver -> SMT.SExpr -> SMT.SExpr -> (String, Int) -> IO [[SMT.Value]]
enumerateProductions s fromSymbol bvType (f, arity) = do
  SMT.simpleCommand s ["push"]
  forM allArgNums $ \argNum -> SMT.declare s (argName argNum) bvType
  SMT.assert s $ (isFProduction f) $$ (fromSymbol : allArgs)
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return $ ret
  where
    allArgNums = [0 .. arity - 1]
    argName i = "prod-val" ++ show i
    allArgs = map productionVal allArgNums
    productionVal i = SMT.Atom $ argName i
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          args <-
            forM allArgNums $ \argNum -> SMT.getExpr s $ productionVal argNum
          let neqConds =
                (flip map) (zip allArgNums args) $ \(i, arg) ->
                  SMT.not ((SMT.value arg) === productionVal i)
          SMT.assert s $ orAll neqConds
          helper (args : accum)
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

unProd :: SMT.Value -> (String, [Integer])
unProd (SMT.Other (SMT.List [SMT.Atom "prod"])) = error "TODO"

--TODO include constratailint stuff
makePred :: SMT.Solver -> [Constr] -> IO (Either [Constr] TreeGrammar) --TODO return solution
makePred s clist = do
  setOptions s
  --SMT.simpleCommand s ["push"]
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      theMaxArity = maxArity subExprs
      numForall = 2 + theMaxArity
      constrNums = allExprNums subExprs
      bvType = SMT.tBits $ toInteger numPreds
      vars = map (\i -> SMT.Atom $ "y_univ_" ++ show i) [1 .. numForall]
      state0 = (initialState vars subExprs)
      funPairs = (Map.toList . arities) state0
      allFreeVars :: [Expr] = filter isVar subExprs
      boolDomArgName = "z_boolDomain"
  makePrelude s (toInteger numPreds) funPairs
  let comp = do
        boolDomPreds <- forM subExprs (booleanDomainClause boolDomArgName)
        constrPreds <- forM clist (constrClause boolDomArgName)
        funDomPreds <-
          withNForalls vars (toInteger $ length subExprs) $ \vars -> do
            predClauses <- forM subExprs functionDomainClause
            isValidDomain <- validDomain
            funClauses <- forM funPairs funClause
            let singleFunClause = andAll funClauses
            enumClauses <- enumeratedDomainClauses funPairs
            return $
              (isValidDomain ==> (andAll predClauses)) /\ singleFunClause /\
              enumClauses
        return (funDomPreds, andAll $ boolDomPreds ++ constrPreds)
  let ((funDomPreds, boolDomPreds), state) = runState comp state0
  --Declare each of our existential variables 
  --Declare our domain function
  --We separate it into a quantified part and non quantified part
  SMT.defineFun
    s
    "booleanDomain"
    [(boolDomArgName, bvType)]
    SMT.tBool
    boolDomPreds
  SMT.declareFun s "functionDomain" [bvType] SMT.tBool
  SMT.defineFun s "domain" [("x", bvType)] SMT.tBool $
    ("booleanDomain" $$ [SMT.Atom "x"]) /\ ("functionDomain" $$ [SMT.Atom "x"])
  --Declare functions to get the enumeration of our domain
  declareEnum s bvType funPairs theMaxArity
  --Delare our constructors
  let funPairs = Map.toList $ arities state
  forM funPairs $ \(f, arity) -> do
    SMT.declareFun s f (replicate arity bvType) bvType
  --Declare our existential variables
  forM (existentialVars state) $ \v -> do
    SMT.declare s v (SMT.tBits $ toInteger numPreds)
    --Assert that each existential variable is in our domain
    SMT.assert s $ "domain" $$ [SMT.Atom v]
  --Assert our domain properties
  SMT.assert s funDomPreds
  result <- SMT.check s
  --TODO minimize?
  case result of
    SMT.Sat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-model"]
      domain <- enumerateDomain s bvType
      putStrLn $ show $ map vshow domain
      forM domain $ \d ->
        forM funPairs $ \funPair@(f, arity) -> do
          prodsFrom <- enumerateProductions s (SMT.value d) bvType funPair
          forM prodsFrom $ \p ->
            putStrLn $
            vshow d ++
            "  ->  " ++ f ++ "(" ++ (List.intercalate ", " $ map vshow p) ++ ")"
      forM allFreeVars $ \v -> do
        prods <- varProductions s v ((predNums state) Map.! v) numPreds
        forM prods $ \prod -> putStrLn $ show v ++ "  ->  " ++ vshow prod
      return $ Right $ error "TODO " --() --TODO return solution
    SMT.Unsat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-unsat-core"]
      return $ Left clist --TODO niminize lemma
    SMT.Unknown -> error "Failed to solve quanitification"
