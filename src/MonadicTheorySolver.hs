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
      let prod = ("prod_" ++ f) $$ vars
      return $
        ("isProduction" $$ [fx, prod]) ===
        ((fx === (f $$ vars)) /\ ("domain" $$ [fx]) /\
         (andAll $ map (\v -> "domain" $$ [v]) vars))
  --Assert that every x has a production
  --This makes sure our finite domain maps to the Herbrand domain
  x <- forallVar
  let hasProd =
        ("domain" $$ [x]) ==> ("isProduction" $$ [x, "productionFor" $$ [x]])
  return $ (andAll results) /\ hasProd

-- declareEnum :: SMT.Solver -> SMT.SExpr -> IO ()
declareEnum s bvType = do
  SMT.declareFun s "isProduction" [bvType, SMT.Atom "Production"] SMT.tBool
  SMT.declareFun s "productionFor" [bvType] (SMT.Atom "Production")
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

unProd :: SMT.Value -> (String, [Integer])
unProd (SMT.Other (SMT.List [SMT.Atom "prod"])) = error "TODO"

--TODO include constratailint stuff
makePred :: SMT.Solver -> [Constr] -> IO (Either [Constr] TreeGrammar) --TODO return solution
makePred s clist = do
  setOptions s
  --SMT.simpleCommand s ["push"]
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      numForall = 2 + maxArity subExprs
      constrNums = allExprNums subExprs
      tBitVec = SMT.tBits $ toInteger numPreds
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
    [(boolDomArgName, SMT.tBits $ toInteger numPreds)]
    SMT.tBool
    boolDomPreds
  SMT.declareFun s "functionDomain" [SMT.tBits $ toInteger numPreds] SMT.tBool
  SMT.defineFun s "domain" [("x", SMT.tBits (toInteger numPreds))] SMT.tBool $
    ("booleanDomain" $$ [SMT.Atom "x"]) /\ ("functionDomain" $$ [SMT.Atom "x"])
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
  SMT.assert s funDomPreds
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
      return $ Right $ error "TODO " --() --TODO return solution
    SMT.Unsat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-unsat-core"]
      return $ Left clist --TODO niminize lemma
    SMT.Unknown -> error "Failed to solve quanitification"
