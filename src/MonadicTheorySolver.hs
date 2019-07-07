{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}

module MonadicTheorySolver where

import SMTHelpers
import Syntax 
import TseitinPredicates
import Data.SBV (SBV, SBool, Symbolic, STuple, (.==), (.&&), (.||), (.=>), Predicate, sNot, sTrue, sFalse, uninterpret)
import qualified Data.SBV.Trans as SBV


import Control.Monad.State
import Control.Monad (when)
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe

import TreeGrammar

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

import ArgParse

-- import Data.Graph
import Data.Constraint (Dict(..))
import GHC.Exts (sortWith)

import Debug.Trace (trace)

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
-- isFProduction f = Fun ("isProductionFor-" ++ vecFunName f)

-- --productionFor i = "productionFor" ++ show i
-- declareProdFuncions ::
--      Integral i => SMT.Solver -> i -> [SExpr] -> [VecFun] -> Int -> IO ()
-- declareProdFuncions s numPreds bvType funs maxArity =
--   forM_ funs $ \f -> do
--     let prodFromName = "fromSymb"
--     let prodFrom = nameToBits numPreds prodFromName
--     let prodToNames =
--           map
--             (\i -> nameToBitNames numPreds $ "toSymb" ++ show i)
--             [0 .. (arity f) - 1]
--     let prodTos :: [BitVector] = map (BitVector . (map SMT.Atom)) prodToNames
--     let prodFromPairs = zip (nameToBitNames numPreds prodFromName) bvType
--     let prodToPairs = zip (concat prodToNames) (repeat SMT.tBool)
--     let fTos = BitVector [bitf $$$ prodTos | bitf <- funToBitFuns numPreds f]
--     let eqToFunRet = vecEq prodFrom fTos
--     let (allInDomain :: SExpr) = andAll $ map (\v -> domain $$$ [v]) prodTos
--     defineFun
--       s
--       (isFProduction f)
--       (prodFromPairs ++ prodToPairs)
--       SMT.tBool
--       (eqToFunRet /\ (domain $$$ [prodFrom]) /\ allInDomain)
  -- forM [0 .. maxArity - 1] $ \argNum -> do
  --   SMT.declareFun s (productionFor argNum) [bvType] bvType
  -- return ()



--Return the constraint that all current quantified universals
--are in the domain
validDomain :: forall n . (BitVector n -> SBool) -> ConfigM n SBool
validDomain domain = do
  vars <- gets universalVars
  case vars of
    [] -> return $ sTrue
    _ -> do
      let varResults = map domain vars
      return $ SBV.sAnd varResults

-- enumerateDomain :: Integral i => SMT.Solver -> i -> [SExpr] -> IO [BitVector]
-- enumerateDomain s numPreds bvType = do
--   SMT.simpleCommand s ["push"]
--   declareVec s "domain-val" bvType
--   SMT.assert s $ domain $$$ [domainVal]
--   ret <- helper []
--   SMT.simpleCommand s ["pop"]
--   return ret
--   where
--     domainVal = nameToBits numPreds "domain-val"
--     helper accum = do
--       putStrLn ";;;; Doing check in theory solver"
--       result <- SMT.check s
--       putStrLn ";;;; Done check in theory solver"
--       case result of
--         SMT.Sat -> do
--           valueExpr <- getBitVec s domainVal
--           SMT.assert s (SMT.not (domainVal `vecEq` valueExpr))
--           helper (valueExpr : accum)
--         SMT.Unsat -> return accum
--         e -> error $ ";;;; TODO Failed quant enumerating domain" ++ show e

--To enumerate through our productions
-- enumerateProductions ::
--      SMT.Solver -> [SExpr] -> [VecFun] -> IO [(BitVector, VecFun, [BitVector])]
-- enumerateProductions s bvType funs
--   -- SMT.assert s $
--   --   (isFProduction f) $$ (unwrap fromSymbol ++ concatMap unwrap allArgs)
--  = do
--   let initialMap = Map.fromList [(f, Set.empty) | f <- funs]
--   helper Set.empty initialMap
--   where
--     productionVal i = nameToBits (length bvType) $ argName i
--     helper ::
--          Set.Set BitVector
--       -> Map.Map VecFun (Set.Set [BitVector])
--       -> IO [(BitVector, VecFun, [BitVector])]
--     helper foundVals foundProds
--       --Declare n variables that we've found
--       --Assert that, for some function, we've found its arguments
--       --but we haven't found the production of our declared values yet for some function
--      = do
--       fResults <-
--         forM funs $ \f ->
--           if (arity f) <= length foundVals
--             then do
--               SMT.simpleCommand s ["push"]
--               let allArgNums = [0 .. (arity f) - 1]
--                   allArgNames = map argName allArgNums
--             --Declare arguments for the function
--               forM_ allArgNames $ \theArg -> declareVec s theArg bvType
--               let allArgs = map productionVal allArgNums
--               let isFound arg =
--                     orAll $ Set.toList $ Set.map (vecEq arg) $ foundVals
--               let prodEq p1 p2 = andAll $ zipWith vecEq p1 p2
--               let prodIsFound prod =
--                     orAll $
--                     Set.toList $ Set.map (prodEq prod) $ foundProds Map.! f
--               --Assert that we've found all the arguments
--               forM_ allArgs $ \arg -> SMT.assert s $ isFound arg
--               --Get expression for the function result
--               let fx = bvApply numPreds f allArgs
--               let prod = fx : allArgs
--               --Assert that we have a production (i.e. everything is in the domain)
--               SMT.assert s $ (isFProduction f) $$$ prod
--               --Assert that we haven't found this production
--               SMT.assert s $ SMT.not (prodIsFound prod)
--               --Look for a solution
--               satResult <- SMT.check s
--               finalResult <-
--                 case satResult of
--                   SMT.Unsat -> return Nothing
--                   SMT.Sat -> do
--                     prodV <- forM prod $ \bv -> getBitVec s bv
--                     return $ Just (f, prodV)
--                   e ->
--                     error $
--                     "Quantification failed in production enum " ++ show e
--               SMT.simpleCommand s ["pop"]
--               return $ finalResult
--             else return Nothing
--       case Maybe.catMaybes fResults of
--         [] ->
--           return $
--           concatMap
--             (\(f, prods) -> [(from, f, to) | (from:to) <- Set.toList prods]) $
--           Map.toList foundProds --We found nothing new
--         newProds -> do
--           let updateMap (f, prod) dict =
--                 Map.insert f (Set.insert prod (dict Map.! f)) dict
--           helper
--             (foundVals `Set.union` (Set.fromList $ map (head . snd) newProds))
--             (foldr updateMap foundProds newProds)
--     numPreds = length bvType
--     argName i = "prod-val-" ++ show i
--     -- helper2 accum = do
--     --   result <- SMT.check s
--     --   case result of
--     --     SMT.Sat -> do
--     --       args <- forM allArgs $ \arg -> getBitVec s arg
--     --       let neqConds =
--     --             (flip map) (zip allArgNums args) $ \(i, arg) ->
--     --               SMT.not (arg `vecEq` (productionVal i))
--     --       SMT.assert s $ orAll neqConds
--     --       helper2 (args : accum)
--     --     SMT.Unsat -> return accum
--     --     _ -> error "TODO Failed quant"

-- varProductions :: SMT.Solver -> PredExpr -> Integer -> Int -> IO [BitVector]
-- varProductions s v i n = do
--   SMT.simpleCommand s ["push"]
--   declareVec s vname $ makeBvType n
--   SMT.assert s $ domain $$$ [matchingVal]
--   SMT.assert s $ ithBit i matchingVal n
--   ret <- helper []
--   SMT.simpleCommand s ["pop"]
--   return ret
--   where
--     vname = "varprod-" ++ (filter isAlphaNum (varName v))
--     matchingVal = nameToBits n vname
--     helper accum = do
--       result <- SMT.check s
--       case result of
--         SMT.Sat -> do
--           prod <- getBitVec s matchingVal
--           SMT.assert s (SMT.not (prod `vecEq` matchingVal))
--           helper (prod : accum)
--         SMT.Unsat -> return accum
--         e -> error $ "TODO Failed quant " ++ show e

defineConstructor ::
  forall n narity . SNat n
  -> String 
  -> SNat narity
  -> Map.Map PredExpr Int
  -> [PredExpr]
  -> (String, VecFun n)
defineConstructor numPreds f numArgs pmap exprs = trace ("Define constructor numPreds: " ++ (show $ sNatToInt numPreds) ++ " with exprs " ++ show exprs) $ 
  let 
    (funForArgs :: [Vec (BitVector n) narity -> SBool] ) = map snd $ {-sortOn fst $ -}  
      (flip map) exprs $ \ e ->  case (e) of
          (PVar _) -> 
            let predNum = pmap Map.! e in (predNum, \ arg -> uninterpret  (f ++ "__" ++ show predNum) (numArgs, numPreds, arg)) 
          ( PFunApp g gargs) -> 
            let 
              retFun =
                case f == g of
                  -- e1 `Union` e2 ->
                  --   ((funFor e1) $$$ allArgs) \/ ((funFor e2) $$$ allArgs)
                  -- e1 `Intersect` e2 ->
                  --   (funFor e1 $$$ allArgs) /\ ((funFor e2) $$$ allArgs)
                  -- Neg e1 -> SMT.not ((funFor e1) $$$ allArgs)
                  True -> \ argVec ->
                      SBV.sAnd $
                      map
                        (\(setArg, argVal) -> pSMT numPreds pmap setArg argVal)
                        $ zip gargs $ vecToList argVec numArgs
                  False -> \ _ -> sFalse 
            in (pmap Map.! e, retFun)
                          
    in trace ("FunForargs:  " ++ show (length funForArgs)) $  (f, VecFun f numArgs $ \ argVec -> makeSVec numPreds (map ($ argVec) funForArgs ))  
    
    

declareOrDefineFuns ::
  forall n . SNat n
  -> Map.Map PredExpr Int
  -> [PredExpr]
  -> [(String, VecFun n)]
declareOrDefineFuns numPreds pmap exprs = 
  let 
    funArities = Map.toList $ getArities  exprs 
  in (flip map) funArities $ \(f,ar) -> 
      case toENat ar of
        (ENat sn_arity ) -> case sn_arity of
          (_ :: SNat nar) -> defineConstructor numPreds f sn_arity pmap exprs  

declareDomain ::
     forall n . SNat n ->  [(BitVector n -> SBool)] ->  BitVector n -> SBool
declareDomain numPreds boolDomPreds arg = 
  let 
    domainToBeDefined = \ arg -> uninterpret "domainToBeDefined" (numPreds, arg)
  in
    domainToBeDefined  arg .&& SBV.sAnd [f arg | f <- boolDomPreds]
  --Declare each of our existential variables 
  --Declare our domain function
  --We separate it into a quantified part and non quantified part
--  = do
--   SMT.declareFun 
--     s
--     "domainToBeSolved"
--      bvType
--     SMT.tBool
--   let bitNames = nameToBitNames numPreds boolDomArgName
--   SMT.defineFun
--     s
--     "domain"
--     (zip bitNames bvType)
--     SMT.tBool
--     (boolDomPreds `SMT.and`  ((Fun "domainToBeSolved") $$ (map SMT.Atom bitNames)))
  -- SMT.declareFun s "functionDomain" bvType SMT.tBool
  --TODO split into separate functions
  -- let domainArgName = "arg-domain"
  -- let domainArg = nameToBits numPreds domainArgName
  -- defineFun
  --   s
  --   domain
  --   (zip (nameToBitNames numPreds domainArgName) bvType)
  --   SMT.tBool $
  --   (booleanDomain $$$ [domainArg]) /\ (funDomain $$$ [domainArg])

--TODO: make this work with single-SAT solver?
-- equalityClasses :: [Constr] -> [Expr] -> [SCC Expr]
-- equalityClasses constrs exprs = sortedSCCs
--   where
--     edges =
--       [(e1, e1, List.nub [e2 | Sub e e2 <- constrs, e == e1]) | e1 <- exprs]
--     sortWithinSCC (AcyclicSCC e) = AcyclicSCC e
--     sortWithinSCC (CyclicSCC l) = CyclicSCC $ sortWith exprInt l
--     theSCCs = map AcyclicSCC exprs --stronglyConnComp edges
--     sortedSCCs = sortWith sccInt $ map sortWithinSCC $ theSCCs
--     exprMap = Map.fromList $ zip exprs [0 ..]
--     exprInt = (exprMap Map.!)
--     sccInt = (exprInt . head . flattenSCC)

--TODO include constratailint stuff
makePredWithSize :: forall n .
     Options
  -> SNat n
  -> (Literal -> SBool)
  -> [Literal]
  -> [PredExpr]
  -> SBool
  -> Int
  -> SBV.Predicate --TODO return solution
makePredWithSize options numPreds  litVarFor litList exprList  litPred theMaxArity
  --setOptions s
 = do
  let log = if (verbose options) then (putStrLn . (";;;; " ++ )) else (\ _ -> return ())
      logIO s = liftIO $ log s 
  
  let numForall = theMaxArity
      -- constrNums = allExprNums subExprs
  (vars :: [BitVector n]) <- forM [1 .. theMaxArity] $ \_ -> forallBitVec numPreds 
  
  --Declare or define the functions for each constructor in our Herbrand universe
  logIO "Declaring constructors"
  
  let allFreeVars :: [PredExpr] = filter isVar exprList  
      -- boolDomArgName = "z_boolDomain"
      -- boolDomArg = nameToBits numPreds boolDomArgName
      
      (predMap, _) = allExprNums  exprList
      funs = declareOrDefineFuns numPreds  predMap exprList
      state0 = 
        Config
        { predNums = predMap
        , configNumPreds = numPreds
        , funVals =
            Map.fromList funs
        , universalVars = vars
        }
        
  logIO ("Lit Vars: " ++ show [(l, litVarFor l) | l <- litList]) 
  logIO ("Pred numbers: " ++ show (predNums state0))
  logIO ("Pred exprs: " ++ show exprList ++ " with length " ++ show (length exprList))
  logIO $ "In theory solver, numBits: " ++ show  (sNatToInt numPreds)
  -- putStrLn $ "Can reduce into " ++ show (length $ eqClasses)
  let comp = do
        liftIO $ putStrLn "In state computation"
        -- boolDomPredList <- forM subExprs (booleanDomainClause boolDomArg)
        --Get the predicates for each positive constraint
        posConstrPreds <- forM litList (posConstrClause litVarFor)
        liftIO $ putStrLn "Got pos constrs"
        --Declare our domain function that ensures all values in the domain satisfy the positive constraints
        let theDomainFun = declareDomain  numPreds  posConstrPreds
        liftIO $ putStrLn "Got domain fun"
        --Get the constraints asserting that there exist values in the domain satisfying the negative constraints
        negConstrPreds <- forM litList (negConstrClause litVarFor numPreds theDomainFun)
        liftIO $ putStrLn "Got neg constrs"
        --Assert that all our universal variables are in the domain
        isValidDomain <- validDomain theDomainFun
        liftIO $ putStrLn "Got valid domain ssesrtion"
        funClauses <- forM (map snd funs) (funClause theDomainFun)
        liftIO $ putStrLn "Got fun closed over domain clauses"
        let singleFunClause = SBV.sAnd funClauses
        -- return $ isValidDomain ==> singleFunClause
        let funDomPreds = (isValidDomain .=> singleFunClause)
            -- enumClauses <- enumeratedDomainClauses funPairs
        return
          ( funDomPreds
          , negConstrPreds)
  ((funDomPreds, negPreds), state) <-  do runStateT comp state0
  logIO "Ran state computation"
  --Declare our domain function and its subfunctions
  
  --Declare functions that determines if a production is valid
  -- declareProdFuncions s numPreds bvType funs theMaxArity
  --Declare our existential variables
  -- log "Declaring existentials"
  -- forM_ (existentialVars state) $ \v -> do
  --   declareVec s v bvType
  
  logIO "About do check SAT"
  return $ (SBV.sAnd negPreds) .&& funDomPreds .&& litPred
  
makePred ::  
  Options
  -> (Literal -> SBool)
  -> [Literal]
  -> SBool
  -> SBV.Predicate
makePred options  litVarFor litList  litPred = 
  let 
    subExprs = orderedSubExpressions litList
    exprList =  Maybe.catMaybes $ map toPredExpr subExprs -- equalityClasses clist subExprs --TODO: bring this back?
  -- (posList, negList) = List.partition isPos clist
    theMaxArity = maxArity subExprs
  in case (toENat (length exprList)) of 
    (ENat (numPreds :: SNat n)) -> 
      
        makePredWithSize options numPreds  litVarFor litList exprList  litPred  theMaxArity
-- printAndReturnResult ::
--      SMT.Solver
--   -> Options
--   -> Int
--   -> [SExpr]
--   -> PredNumConfig
--   -> [VecFun]
--   -> [PredExpr]
--   -> IO (Either a b)
-- printAndReturnResult s options numPreds bvType state funs allFreeVars
--   -- SMT.command s $ SMT.List [SMT.Atom "get-model"]
--  = do
--   case getModel options of
--     True -> do
--       domain <- enumerateDomain s numPreds bvType
--       putStrLn $ ";;;; DOMAIN: " ++ show domain
--       prodsFrom <- enumerateProductions s bvType funs
--         --TODO do based on options
--       forM_ prodsFrom $ \(from, f, to) ->
--         putStrLn $ show from ++ "  ->  " ++ show f ++ show to
--       forM_ allFreeVars $ \v -> do
--         prods <- varProductions s v ((predNums state) Map.! v) numPreds
--         forM prods $ \prod -> putStrLn $ ";;;; " ++ varName v ++ "  ->  " ++ (show prod)
--     False -> return ()
--   return $ Right $ error "TODO " --() --TODO return solution
