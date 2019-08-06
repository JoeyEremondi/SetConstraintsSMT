{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

module MonadicTheorySolver where

import SMTHelpers
import Syntax
import TseitinPredicates

import Control.Monad.State
import Control.Monad (when)
import qualified Data.Data as Data
import Data.List as List
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe
import qualified SimpleSMT as SMT
import SimpleSMT (SExpr)
import TreeGrammar

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

import ArgParse

import Data.Graph

import GHC.Exts (sortWith)

makeBvType :: Integral a => a -> [SMT.SExpr]
makeBvType n = replicate (fromInteger $ toInteger n) SMT.tBool

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
isFProduction f = Fun ("isProductionFor-" ++ vecFunName f)

--productionFor i = "productionFor" ++ show i
declareProdFuncions ::
     Integral i => SMT.Solver -> i -> [SExpr] -> [VecFun] -> Int -> IO ()
declareProdFuncions s numPreds bvType funs maxArity =
  forM_ funs $ \f -> do
    let prodFromName = "fromSymb"
    let prodFrom = nameToBits numPreds prodFromName
    let prodToNames =
          map
            (\i -> nameToBitNames numPreds $ "toSymb" ++ show i)
            [0 .. (arity f) - 1]
    let prodTos :: [BitVector] = map (BitVector . (map SMT.Atom)) prodToNames
    let prodFromPairs = zip (nameToBitNames numPreds prodFromName) bvType
    let prodToPairs = zip (concat prodToNames) (repeat SMT.tBool)
    let fTos = BitVector [bitf $$$ prodTos | bitf <- funToBitFuns numPreds f]
    let eqToFunRet = vecEq prodFrom fTos
    let (allInDomain :: SExpr) = andAll $ map (\v -> domain $$$ [v]) prodTos
    defineFun
      s
      (isFProduction f)
      (prodFromPairs ++ prodToPairs)
      SMT.tBool
      (eqToFunRet /\ (domain $$$ [prodFrom]) /\ allInDomain)
  -- forM [0 .. maxArity - 1] $ \argNum -> do
  --   SMT.declareFun s (productionFor argNum) [bvType] bvType
  -- return ()

withNForalls ::
     [BitVector] -> Integer -> ([BitVector] -> ConfigM SExpr) -> ConfigM SExpr
withNForalls vars numBits comp | numBits == 0 || null vars = comp []
withNForalls vars numBits comp = do
  result <- comp vars
  return $ SMT.List [SMT.Atom "forall", SMT.List varTypes, result]
  where
    varTypes = [SMT.List [bit, SMT.tBool] | bv <- vars, bit <- bitList bv]

--Return the constraint that all current quantified universals
--are in the domain
validDomain :: ConfigM SExpr
validDomain = do
  vars <- gets universalVars
  case vars of
    [] -> return $ SMT.bool True
    _ -> do
      let varResults = map (\x -> domain $$$ [x]) vars
      return $ andAll varResults

enumerateDomain :: Integral i => SMT.Solver -> i -> [SExpr] -> IO [BitVector]
enumerateDomain s numPreds bvType = do
  SMT.simpleCommand s ["push"]
  declareVec s "domain-val" bvType
  SMT.assert s $ domain $$$ [domainVal]
  ret <- helper []
  SMT.simpleCommand s ["pop"]
  return ret
  where
    domainVal = nameToBits numPreds "domain-val"
    helper accum = do
      putStrLn ";;;; Doing check in theory solver"
      result <- SMT.check s
      putStrLn ";;;; Done check in theory solver"
      case result of
        SMT.Sat -> do
          valueExpr <- getBitVec s domainVal
          SMT.assert s (SMT.not (domainVal `vecEq` valueExpr))
          helper (valueExpr : accum)
        SMT.Unsat -> return accum
        e -> error $ ";;;; TODO Failed quant enumerating domain" ++ show e

--To enumerate through our productions
enumerateProductions ::
     SMT.Solver -> [SExpr] -> [VecFun] -> IO [(BitVector, VecFun, [BitVector])]
enumerateProductions s bvType funs
  -- SMT.assert s $
  --   (isFProduction f) $$ (unwrap fromSymbol ++ concatMap unwrap allArgs)
 = do
  let initialMap = Map.fromList [(f, Set.empty) | f <- funs]
  helper Set.empty initialMap
  where
    productionVal i = nameToBits (length bvType) $ argName i
    helper ::
         Set.Set BitVector
      -> Map.Map VecFun (Set.Set [BitVector])
      -> IO [(BitVector, VecFun, [BitVector])]
    helper foundVals foundProds
      --Declare n variables that we've found
      --Assert that, for some function, we've found its arguments
      --but we haven't found the production of our declared values yet for some function
     = do
      fResults <-
        forM funs $ \f ->
          if (arity f) <= length foundVals
            then do
              SMT.simpleCommand s ["push"]
              let allArgNums = [0 .. (arity f) - 1]
                  allArgNames = map argName allArgNums
            --Declare arguments for the function
              forM_ allArgNames $ \theArg -> declareVec s theArg bvType
              let allArgs = map productionVal allArgNums
              let isFound arg =
                    orAll $ Set.toList $ Set.map (vecEq arg) $ foundVals
              let prodEq p1 p2 = andAll $ zipWith vecEq p1 p2
              let prodIsFound prod =
                    orAll $
                    Set.toList $ Set.map (prodEq prod) $ foundProds Map.! f
              --Assert that we've found all the arguments
              forM_ allArgs $ \arg -> SMT.assert s $ isFound arg
              --Get expression for the function result
              let fx = bvApply numPreds f allArgs
              let prod = fx : allArgs
              --Assert that we have a production (i.e. everything is in the domain)
              SMT.assert s $ (isFProduction f) $$$ prod
              --Assert that we haven't found this production
              SMT.assert s $ SMT.not (prodIsFound prod)
              --Look for a solution
              satResult <- SMT.check s
              finalResult <-
                case satResult of
                  SMT.Unsat -> return Nothing
                  SMT.Sat -> do
                    prodV <- forM prod $ \bv -> getBitVec s bv
                    return $ Just (f, prodV)
                  e ->
                    error $
                    "Quantification failed in production enum " ++ show e
              SMT.simpleCommand s ["pop"]
              return $ finalResult
            else return Nothing
      case Maybe.catMaybes fResults of
        [] ->
          return $
          concatMap
            (\(f, prods) -> [(from, f, to) | (from:to) <- Set.toList prods]) $
          Map.toList foundProds --We found nothing new
        newProds -> do
          let updateMap (f, prod) dict =
                Map.insert f (Set.insert prod (dict Map.! f)) dict
          helper
            (foundVals `Set.union` (Set.fromList $ map (head . snd) newProds))
            (foldr updateMap foundProds newProds)
    numPreds = length bvType
    argName i = "prod-val-" ++ show i
    -- helper2 accum = do
    --   result <- SMT.check s
    --   case result of
    --     SMT.Sat -> do
    --       args <- forM allArgs $ \arg -> getBitVec s arg
    --       let neqConds =
    --             (flip map) (zip allArgNums args) $ \(i, arg) ->
    --               SMT.not (arg `vecEq` (productionVal i))
    --       SMT.assert s $ orAll neqConds
    --       helper2 (args : accum)
    --     SMT.Unsat -> return accum
    --     _ -> error "TODO Failed quant"

varProductions :: SMT.Solver -> PredExpr -> Integer -> Int -> IO [BitVector]
varProductions s v i n = do
  SMT.simpleCommand s ["push"]
  declareVec s vname $ makeBvType n
  SMT.assert s $ domain $$$ [matchingVal]
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
          prod <- getBitVec s matchingVal
          SMT.assert s (SMT.not (prod `vecEq` matchingVal))
          helper (prod : accum)
        SMT.Unsat -> return accum
        e -> error $ "TODO Failed quant " ++ show e

declareOrDefineFuns ::
     Integral t
  => SMT.Solver
  -> t
  -> [SExpr]
  -> PredNumConfig
  -> [SCC PredExpr]
  -> IO [[()]]
declareOrDefineFuns s numPreds bvType state sccs = do
  let funs = Map.elems $ funVals state
  forM funs $ \f -> do
    let allArgNums = [0 .. (arity f) - 1]
    let allArgNames = map (\arg -> ("f-arg-" ++ show arg)) allArgNums
    let allArgs =
          map (\arg -> nameToBits numPreds $ ("f-arg-" ++ show arg)) allArgNums
    let funBitNames = funToBitFuns numPreds f
    let bitFor expr =  (predNums state) Map.! expr
    let funFor e =
          case fromIntegral i < length funBitNames of
            True -> (funBitNames !!! (fromIntegral i))
          where
            i = bitFor e
    let canDefine scc =
          case scc of
            AcyclicSCC (PVar _) -> False
            AcyclicSCC _ -> True
            CyclicSCC _ -> False --TODO check for self-reference
        (toDefine, toDeclare) = partition canDefine sccs
    --Define the ith-bit functions for our constructor when we can
    --Otherwise, just declare them
    forM_ toDeclare $ \scc
      --TODO put back define case?
      -- putStrLn $ "Declaring SCC" ++ show (flattenSCC scc) ++ "for " ++ show f
     ->
      case scc of
        AcyclicSCC expr@(PVar v) -> do
          declareFun
            s
            (funFor expr)
            (concat $ replicate (arity f) bvType)
            SMT.tBool
          return ()
        CyclicSCC exprList@(expr:_) -> do
          declareFun
            s
            (funFor expr)
            (concat $ replicate (arity f) bvType)
            SMT.tBool
          return ()
    forM toDefine $ \scc
      -- putStrLn $ "Defining SCC" ++ show (flattenSCC scc) ++ "for " ++ show f
     ->
      case scc of
        AcyclicSCC expr
          -- putStrLn $ "** Defining function for " ++ show expr
         -> do
          let (PFunApp g gargs) = expr
          let funBody =
                case vecFunName f == g of
                  -- e1 `Union` e2 ->
                  --   ((funFor e1) $$$ allArgs) \/ ((funFor e2) $$$ allArgs)
                  -- e1 `Intersect` e2 ->
                  --   (funFor e1 $$$ allArgs) /\ ((funFor e2) $$$ allArgs)
                  -- Neg e1 -> SMT.not ((funFor e1) $$$ allArgs)
                  True ->
                      andAll $
                      map
                        (\(setArg, argVal) -> pSMT state setArg argVal)
                        (zip gargs allArgs)
                  False -> SMT.bool False
                  -- Top -> SMT.bool True
                  -- Bottom -> SMT.bool False
          let argPairs =
                concatMap
                  (\argName ->
                     zip (nameToBitNames (length bvType) argName) bvType)
                  allArgNames
          defineFun s (funFor expr) argPairs SMT.tBool funBody
          return ()

declareDomain ::
     Integral t => SMT.Solver -> t -> [SExpr] -> SExpr -> [Char] -> IO SExpr
declareDomain s numPreds bvType boolDomPreds boolDomArgName
  --Declare each of our existential variables 
  --Declare our domain function
  --We separate it into a quantified part and non quantified part
 = do
  SMT.declareFun 
    s
    "domainToBeSolved"
     bvType
    SMT.tBool
  let bitNames = nameToBitNames numPreds boolDomArgName
  SMT.defineFun
    s
    "domain"
    (zip bitNames bvType)
    SMT.tBool
    (boolDomPreds `SMT.and`  ((Fun "domainToBeSolved") $$ (map SMT.Atom bitNames)))
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
makePred ::
     SMT.Solver
  -> Options
  -> (Literal -> SMT.SExpr)
  -> [Literal]
  -> IO (Either [Constr] TreeGrammar) --TODO return solution
makePred s options litVarFor litList
  --setOptions s
 = do
  let log = if (verbose options) then (putStrLn . (";;;; " ++ )) else (\ _ -> return ())
  let subExprs = orderedSubExpressions litList
      -- (posList, negList) = List.partition isPos clist
      theMaxArity = maxArity subExprs
      numForall = theMaxArity
      -- constrNums = allExprNums subExprs
      bvType = makeBvType numPreds
      vars =
        map (\i -> nameToBits numPreds $ "y_univ_" ++ show i) [1 .. numForall] 
      state0 = (initialState numPreds vars (Maybe.mapMaybe toPredExpr subExprs) $ map flattenSCC eqClasses)
      
      funs :: [VecFun] = Map.elems $ funVals state0
      allFreeVars :: [PredExpr] = filter isVar $ Maybe.catMaybes $ map toPredExpr subExprs  
      boolDomArgName = "z_boolDomain"
      boolDomArg = nameToBits numPreds boolDomArgName
      eqClasses = map AcyclicSCC  $ Maybe.catMaybes $ map toPredExpr subExprs -- equalityClasses clist subExprs --TODO: bring this back?
      numPreds =  length eqClasses
  log ("Lit Vars: " ++ show [(l, litVarFor l) | l <- litList]) 
  log ("Pred numbers: " ++ show (predNums state0))
  log $ "In theory solver, numBits: " ++ show numPreds
  -- putStrLn $ "Can reduce into " ++ show (length $ eqClasses)
  let comp = do
        -- boolDomPredList <- forM subExprs (booleanDomainClause boolDomArg)
        posConstrPreds <- forM litList (posConstrClause litVarFor boolDomArg)
        negConstrPreds <- forM litList (negConstrClause litVarFor numPreds)
        funDomPreds <-
          withNForalls vars (toInteger numPreds) $ \vars
            --TODO only do clauses for undefined function vars
           -> do
            -- predClauses <- forM subExprs functionDomainClause
            isValidDomain <- validDomain
            funClauses <- forM funs funClause
            let singleFunClause = andAll funClauses
            -- return $ isValidDomain ==> singleFunClause
            return $ (isValidDomain ==> singleFunClause)
            -- enumClauses <- enumeratedDomainClauses funPairs
        constClauses <- (fmap Maybe.catMaybes) $ forM funs constClause 
        return
          ( funDomPreds
          , andAll $ posConstrPreds {- ++ boolDomPredList -} 
          , constClauses ++ negConstrPreds)
  let ((funDomPreds, boolDomPreds, negPreds), state) = runState comp state0
  --Declare our domain function and its subfunctions
  log "Declaring domain"
  declareDomain s numPreds bvType boolDomPreds boolDomArgName
  --Declare or define the functions for each constructor in our Herbrand universe
  log "Declaring constructors"
  declareOrDefineFuns s numPreds bvType state eqClasses
  --Declare functions that determines if a production is valid
  -- declareProdFuncions s numPreds bvType funs theMaxArity
  --Declare our existential variables
  log "Declaring existentials"
  forM_ (existentialVars state) $ \v -> do
    declareVec s v bvType
  --Assert the properties of each existential variable
  log "Assert existential properties"
  forM_ negPreds $ SMT.assert s
  --Assert our domain properties
  log "Asserting function domain properties"
  SMT.assert s funDomPreds
  log "About do check SAT"
  log ";;;;;;;;END OF SMT FILE"
  result <- SMT.check s
  --TODO minimize?
  case result of
    SMT.Sat ->
      printAndReturnResult s options numPreds bvType state funs allFreeVars
    SMT.Unsat -> return $ Left [] --TODO put something useful here
    SMT.Unknown -> error "Failed to solve quanitification"

printAndReturnResult ::
     SMT.Solver
  -> Options
  -> Int
  -> [SExpr]
  -> PredNumConfig
  -> [VecFun]
  -> [PredExpr]
  -> IO (Either a b)
printAndReturnResult s options numPreds bvType state funs allFreeVars
  -- SMT.command s $ SMT.List [SMT.Atom "get-model"]
 = do
  case getModel options of
    True -> do
      domain <- enumerateDomain s numPreds bvType
      putStrLn $ ";;;; DOMAIN: " ++ show domain
      prodsFrom <- enumerateProductions s bvType funs
        --TODO do based on options
      forM_ prodsFrom $ \(from, f, to) ->
        putStrLn $ show from ++ "  ->  " ++ show f ++ show to
      forM_ allFreeVars $ \v -> do
        prods <- varProductions s v ((predNums state) Map.! v) numPreds
        forM prods $ \prod -> putStrLn $ ";;;; " ++ varName v ++ "  ->  " ++ (show prod)
    False -> return ()
  return $ Right $ error "TODO " --() --TODO return solution
