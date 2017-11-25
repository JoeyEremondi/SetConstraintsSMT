{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module MonadicTheorySolver where

import SMTHelpers
import qualified SimpleSMT as SMT hiding (tBits)
import Syntax
import TseitinPredicates

import Control.Monad.State
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe
import qualified SimpleSMT as SMT
import SimpleSMT (SExpr)

import SMTHelpers
import TreeGrammar

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

makeBvType :: Integral a => a -> [SMT.SExpr]
makeBvType n = replicate (fromInteger $ toInteger n) SMT.tBool

makePrelude s n funPairs
  -- let bvTypeS = sshow $ _ n
  -- let variants =
  --       (flip map) funPairs $ \(f, arity) ->
  --         let symbols =
  --               List.intercalate " " $
  --               (flip map) [0 .. arity - 1] $ \i ->
  --                 " (toSymb_" ++ f ++ "_" ++ show i ++ " " ++ bvTypeS ++ " )"
  --         in "(prod_" ++ f ++ symbols ++ ")"
  -- let Just (datatypeCommand, _) =
  --       SMT.readSExpr
  --         ("(declare-datatypes () ((Production " ++
  --          (List.intercalate " " variants) ++ ")))")
  --SMT.command s datatypeCommand
 = do
  return ()

--Clauses asserting that our production checking function is correct
--and asserting that each value in our domain is reachable through some production
--TODO rename
-- enumeratedDomainClauses funPairs
--   --Assert that every x has a production
--   --This makes sure our finite domain maps to the Herbrand domain
--  = do
--   x <- forallVar
--   --We or each of these conditions
--   let hasProdConds =
--         (flip map) funPairs $ \(f, arity) -> do
--           ("domain" $$ [x]) ==>
--             ((isFProduction f) $$
--              (x : [productionFor i $$ [x] | i <- [0 .. arity - 1]]))
--   return (orAll hasProdConds)
isFProduction (VecFun f) = Fun ("isProductionFor-" ++ f)

--productionFor i = "productionFor" ++ show i
declareEnum ::
     Integral i => SMT.Solver -> i -> [SExpr] -> [(VecFun, Int)] -> Int -> IO ()
declareEnum s numPreds bvType funPairs maxArity = do
  forM funPairs $ \(f, arity) -> do
    let prodFromName = "fromSymb"
    let prodFrom = nameToBits numPreds prodFromName
    let prodToNames =
          map
            (\i -> nameToBitNames numPreds $ "toSymb" ++ show i)
            [0 .. arity - 1]
    let prodTos :: [BitVector] = map (BitVector . (map SMT.Atom)) prodToNames
    let prodFromPairs = zip (nameToBitNames numPreds prodFromName) bvType
    let prodToPairs = zip (concat prodToNames) (repeat SMT.tBool)
    let fTos =
          BitVector
            [ bitf $$ (concat $ map unwrap $ prodTos)
            | bitf <- funToBitFuns numPreds f
            ]
    let eqToFunRet = vecEq prodFrom fTos
    let (allInDomain :: SExpr) =
          andAll $ map (\v -> domain $$ (unwrap v)) prodTos
    defineFun
      s
      (isFProduction f)
      (prodToPairs ++ prodFromPairs)
      SMT.tBool
      (eqToFunRet /\ (domain $$ unwrap prodFrom) /\ allInDomain)
  -- forM [0 .. maxArity - 1] $ \argNum -> do
  --   SMT.declareFun s (productionFor argNum) [bvType] bvType
  return ()

withNForalls ::
     [BitVector] -> Integer -> ([BitVector] -> ConfigM SExpr) -> ConfigM SExpr
withNForalls vars numBits comp = do
  result <- comp vars
  return $ SMT.List $ [SMT.Atom "forall", SMT.List (varTypes), result]
  where
    varTypes = [SMT.List [bit, SMT.tBool] | bv <- vars, bit <- unwrap bv]

validDomain :: ConfigM SExpr
validDomain = do
  vars <- universalVars <$> get
  let varResults = (flip map) vars (\x -> domain $$ (unwrap x))
  return $ andAll varResults

enumerateDomain :: Integral i => SMT.Solver -> i -> [SExpr] -> IO [BitVector]
enumerateDomain s numPreds bvType = do
  SMT.simpleCommand s ["push"]
  declareVec s ("domain-val") bvType
  SMT.assert s $ domain $$ (unwrap domainVal)
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    domainVal = nameToBits numPreds "domain-val"
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          valueExpr <- getBitVec s domainVal
          SMT.assert s (SMT.not (domainVal `vecEq` valueExpr))
          helper (valueExpr : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant enumerating domain"

enumerateProductions ::
     SMT.Solver -> BitVector -> [SExpr] -> (VecFun, Int) -> IO [[BitVector]]
enumerateProductions s fromSymbol bvType (f, arity) = do
  SMT.simpleCommand s ["push"]
  forM allArgNums $ \argNum -> declareVec s (argName argNum) bvType
  SMT.assert s $
    (isFProduction f) $$ (unwrap fromSymbol ++ concatMap unwrap allArgs)
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return $ ret
  where
    numPreds = length bvType
    allArgNums = [0 .. arity - 1]
    argName i = "prod-val-" ++ show i
    allArgs = map productionVal allArgNums
    productionVal i = nameToBits (length bvType) $ argName i
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          args <- forM allArgs $ \arg -> getBitVec s arg
          let neqConds =
                (flip map) (zip allArgNums args) $ \(i, arg) ->
                  SMT.not (arg `vecEq` (productionVal i))
          SMT.assert s $ orAll neqConds
          helper (args : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant"

varProductions :: SMT.Solver -> Expr -> Integer -> Int -> IO [[SMT.Value]]
varProductions s v i n = do
  SMT.simpleCommand s ["push"]
  declareVec s vname $ makeBvType n
  SMT.assert s $ domain $$ (unwrap matchingVal)
  SMT.assert s $ ithBit i matchingVal n
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    vname = "varprod-" ++ (filter isAlphaNum (varName v))
    matchingVal = nameToBits n vname
    helper accum = do
      result <- SMT.check s
      case result of
        SMT.Sat -> do
          prodBits <- forM (unwrap matchingVal) $ \bit -> (SMT.getExpr s bit)
          let prodEqConds =
                zipWith (===) (map SMT.value prodBits) (unwrap matchingVal)
          SMT.assert s (SMT.not (andAll prodEqConds))
          helper (prodBits : accum)
        SMT.Unsat -> return accum
        _ -> error "TODO Failed quant"

unProd :: SMT.Value -> (String, [Integer])
unProd (SMT.Other (SMT.List [SMT.Atom "prod"])) = error "TODO"

--TODO include constratailint stuff
makePred :: SMT.Solver -> [Constr] -> IO (Either [Constr] TreeGrammar) --TODO return solution
makePred s clist
  --setOptions s
 = do
  let subExprs = constrSubExprs clist
      numPreds = length subExprs
      theMaxArity = maxArity subExprs
      numForall = 2 + theMaxArity
      constrNums = allExprNums subExprs
      bvType = makeBvType numPreds
      vars =
        map (\i -> nameToBits numPreds $ "y_univ_" ++ show i) [1 .. numForall]
      state0 = (initialState vars subExprs)
      funPairs = (Map.toList . arities) state0
      allFreeVars :: [Expr] = filter isVar subExprs
      boolDomArgName = "z_boolDomain"
      boolDomArg = nameToBits numPreds boolDomArgName
  makePrelude s (toInteger numPreds) funPairs
  let comp = do
        boolDomPredList <- forM subExprs (booleanDomainClause boolDomArg)
        constrPreds <- forM clist (constrClause boolDomArg)
        funDomPreds <-
          withNForalls vars (toInteger $ length subExprs) $ \vars -> do
            predClauses <- forM subExprs functionDomainClause
            isValidDomain <- validDomain
            funClauses <- forM funPairs funClause
            let singleFunClause = andAll funClauses
            -- enumClauses <- enumeratedDomainClauses funPairs
            return $ (isValidDomain ==> (andAll predClauses)) /\ singleFunClause
        return (funDomPreds, andAll $ boolDomPredList ++ constrPreds)
  let ((funDomPreds, boolDomPreds), state) = runState comp state0
  --Declare each of our existential variables 
  --Declare our domain function
  --We separate it into a quantified part and non quantified part
  SMT.defineFun
    s
    "booleanDomain"
    (zip (nameToBitNames numPreds boolDomArgName) bvType)
    SMT.tBool
    boolDomPreds
  SMT.declareFun s "functionDomain" bvType SMT.tBool
  --TODO split into separate functions
  let domainArgName = "arg-domain"
  let domainArg = nameToBits numPreds domainArgName
  defineFun
    s
    domain
    (zip (nameToBitNames numPreds domainArgName) bvType)
    SMT.tBool $
    (booleanDomain $$ unwrap domainArg) /\ (funDomain $$ unwrap domainArg)
  --Delare our constructors
  let funPairs = Map.toList $ arities state
  forM funPairs $ \(f, arity) -> do
    let allArgNums = [0 .. arity - 1]
    let allArgNames = map (\arg -> ("f-arg-" ++ show arg)) allArgNums
    let allArgs =
          map (\arg -> nameToBits numPreds $ ("f-arg-" ++ show arg)) allArgNums
    let allArgsConcat = concatMap unwrap allArgs
    let funBitNames = funToBitFuns numPreds f
    let bitFor expr = (predNums state) Map.! expr
    let funFor e =
          case fromIntegral i < length funBitNames of
            True -> (funBitNames List.!! (fromIntegral i))
          where
            i = bitFor e
    --Declare ith bit functions before we define
    --Define the ith-bit functions for our constructor
    forM (reverse subExprs) $ \expr -> do
      case expr of
        Var v -> do
          declareFun s (funFor expr) (concat $ replicate arity bvType) SMT.tBool
          return ()
        _ -> do
          let funBody =
                case expr of
                  e1 `Union` e2 ->
                    ((funFor e1) $$ allArgsConcat) \/
                    ((funFor e2) $$ allArgsConcat)
                  e1 `Intersect` e2 ->
                    ((funFor e1) $$ allArgsConcat) /\
                    ((funFor e2) $$ allArgsConcat)
                  Neg e1 -> SMT.not ((funFor e1) $$ allArgsConcat)
                  FunApp g gargs
                    | f == g ->
                      andAll $
                      (flip map)
                        (zip gargs allArgs)
                        (\(setArg, inputArg) ->
                           ithBit (bitFor setArg) inputArg numPreds)
                    | f /= g -> SMT.bool False
                  Top -> SMT.bool True
                  Bottom -> SMT.bool False
          let argPairs =
                concatMap
                  (\argName ->
                     zip (nameToBitNames (length bvType) argName) bvType)
                  allArgNames
          defineFun s (funFor expr) argPairs SMT.tBool funBody
          return ()
  --Declare functions to get the enumeration of our domain and productions
  declareEnum s numPreds bvType funPairs theMaxArity
  --Declare our existential variables
  forM (existentialVars state) $ \v -> do
    declareVec s v bvType
    --Assert that each existential variable is in our domain
    SMT.assert s $ domain $$ [SMT.Atom v]
  --Assert our domain properties
  SMT.assert s funDomPreds
  result <- SMT.check s
  --TODO minimize?
  case result of
    SMT.Sat -> do
      SMT.command s $ SMT.List [SMT.Atom "get-model"]
      domain <- enumerateDomain s numPreds bvType
      putStrLn $ "DOMAIN: " ++ show domain
      forM domain $ \d ->
        forM funPairs $ \funPair@(f, arity) -> do
          prodsFrom <- enumerateProductions s d bvType funPair
          forM prodsFrom $ \p ->
            putStrLn $ show d ++ "  ->  " ++ show f ++ "(" ++ show p ++ ")"
      forM allFreeVars $ \v -> do
        prods <- varProductions s v ((predNums state) Map.! v) numPreds
        forM prods $ \prod -> putStrLn $ show v ++ "  ->  " ++ (show prod)
      return $ Right $ error "TODO " --() --TODO return solution
    SMT.Unsat -> do
      return $ Left clist --TODO niminize lemma
    SMT.Unknown -> error "Failed to solve quanitification"
