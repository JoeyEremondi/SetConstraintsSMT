module SolveSetConstraints where

import ArgParse
import Control.Monad
import Data.Char (intToDigit)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified MonadicTheorySolver as Solver
import Numeric (showIntAtBase)
import SMTHelpers
import qualified Z3.Monad as Z3
import qualified Z3.Base as Z3Base
import qualified Z3.Base.C as C


import Control.Monad.IO.Class (liftIO)

import Syntax

import Data.Either (rights)
import Data.Graph
import Data.Tree (flatten)
import Data.Tuple (swap)

import  Z3.Opts


formulaForCExpr :: (Literal -> SBool) -> CExpr -> ZSBool
formulaForCExpr litIdentifierFor cexp =
  case cexp of
    (s1 `CSubset` s2) -> return $ litIdentifierFor $ Literal (s1, s2)
    (CAnd cexprs) -> sAnd =<< mapM self cexprs
    (COr cexprs) -> sOr =<< mapM self cexprs
    (c1 `CImplies` c2) -> self c1 ..=> self c2
    (c1 `CIff` c2) -> self c1 ..== self c2
    (CNot c1) -> sNot =<< self c1
  where
    self = formulaForCExpr litIdentifierFor

makeLemma :: (Literal -> SBool) -> [Constr] -> ZSBool
makeLemma litNum clist = sNot =<< sAnd =<< mapM helper clist 
  where
    helper c =
      case c of
        e1 `Sub` e2 -> return $ litNum $ Literal (e1, e2)
        e1 `NotSub` e2 -> sNot $ litNum $ Literal (e1, e2)


        


solveSetConstraints :: Options -> (CExpr) -> IO (Either String ()) 
solveSetConstraints options cWithoutNonTrivial
  --Declare our inclusion function
  --
 = do
  let log = if (verbose options) then (putStrLn . (";;;; " ++ )) else (\ _ -> return ())
  log $ "cInitial: " ++ show cInitial
  log $ "Got initial expr list:" ++ show exprList 
  -- SMT.declareFun s "literalValue" litType SMT.tBool
  -- forM_ literalNames $ _ -- \(SMT.Atom ln) -> SMT.declare s ln SMT.tBool
  --Assert the SMT version of our expression
  
  log $
    "Done asserting formula, " ++ 
     show (Set.size lits) ++ " literals total"
  -- log $
  --   "Partitioned into " ++
  --   show (length litPartitions) ++ " subproblems: " ++ show litPartitions
  -- forM [(e1, e2) | e1 <- exprList, e2 <- exprList] $
  --   uncurry subsetLemmaFor
  log "Done asserting subset properties"
  -- assertTransitive
  -- log "Done asserting transitivity"
  

  
  --TODO: assert litFormula and makePred
  -- let verbosity  = if verbose options then (10 :: Int ) else 0
  -- let opts = stdOpts +? (opt "trace" True) +? (opt "smt.mbqi" True)
  result <- Z3.evalZ3 $ do
    Z3.push
    params <- Z3.mkParams
    mbqi <- Z3.mkStringSymbol ":smt.mbqi"
    produceModels <- Z3.mkStringSymbol ":model"
    Z3.paramsSetBool params mbqi True
    Z3.paramsSetBool params produceModels (verbose options)
    Z3.solverSetParams params
    literalNames <- forM litList $ \ l -> Z3.mkFreshBoolVar "literal_"
    let litMap = Map.fromList $ flip zip literalNames $ litList
    let litFun l =
          case (Map.lookup l litMap) of 
            Nothing -> error ("Key" ++ show l ++ " not in map " )
            Just x -> x
    litFormula <- formulaForCExpr litFun cComplete
    pred <- Solver.makePred options  litFun (Set.toList lits) litFormula
    
    when (verbose options) $ do
      -- dummy <- Z3.mkBool True
      -- Z3.assert dummy
      -- (result, Just model) <- Z3.solverCheckAndGetModel
      -- liftIO $ putStrLn ("Result: " ++ show result )
      -- funs <- Z3.getFuncs model
      -- consts <- Z3.getConsts model
      -- declStrings <- forM (funs ++ consts) Z3.funcDeclToString 
      -- let decls = List.intercalate "\n;;\n" declStrings  
      -- liftIO $ putStrLn $ ";;;;Model\n" ++ decls ++ "\n;;;End Model\n"
      sPred <-  Z3.astToString pred
      liftIO $ putStrLn sPred 
    Z3.assert pred
    ret <- Z3.check
    Z3.pop 1
    return ret
  case result of 
    Z3.Sat -> do
      log $ ";; Found solution"
      return $ Right () --  <$> putStrLn "Found Solution"
    Z3.Unsat -> do
      log $ ";; Did not find solution"
      -- when (verbose options) (SMT.simpleCommand s ["get-unsat-core"]) 
      return $ Left "Could not find solution to constraints"
    Z3.Undef -> error "Could not solve quantified constraints"
  
  
    -- exprSubset lhs rhs = (Fun "literalValue") $$$ [exprFun lhs, exprFun rhs]
  where
    nonTrivial = (CNot $ Top `CSubset` Bottom)
    cInitial = 
          case cWithoutNonTrivial of
            CAnd l -> CAnd $ nonTrivial : l
            _ -> CAnd [nonTrivial, cWithoutNonTrivial]    
    cComplete = cInitial --We don't need a bunch of lemmas if we use Z3's SMT solver
      --And if we do, then we should assert them for the literal variables 
    -- CAnd [cInter, cTransitive] --TODO add more
      -- map (\i -> SMT.Atom $ "literal_" ++ show i) [0 .. length lits - 1]
    -- baseLits = literalsInCExpr cBase
    lits = literalsInCExpr cInitial
    litList = Set.toList lits
    
    litRightSidesMap =
      Map.fromList
        [ (e1, [e2 | Literal (e1', e2) <- litList, e1' == e1])
        | Literal (e1, _) <- litList
        ]
    -- litPartitions = partitionLiterals
    -- numBits = ceiling $ logBase 2 (toFloat $ Set.size lits)
    -- litType = replicate numBits SMT.tBool
    -- baseExprs = exprsInCExpr cBase
    -- baseExprList = Set.toList baseExprs
    exprs = exprsInCExpr cInitial
    exprList = Set.toList exprs
    -- numPredInt = length $ List.nub exprList
    -- exprMap = Map.fromList $ zip (exprList) [0 ..]
    -- exprFun = (intToBits numBits) . (exprMap Map.!)
    -- solverLoop i = do
    --   putStrLn $ "SolverLoop" ++ show i
    --   result <- SMT.check s
    --   case result of
    --     SMT.Unsat -> putStrLn $ "UNSAT in " ++ show i ++ " theory iterations"
    --     SMT.Unknown -> error "Shouldn't have quantifiers in solver loop"
    --     SMT.Sat -> do
    --       putStrLn "Solver loop SAT, trying theory solver"
    --       model <- SMT.command s $ SMT.List [SMT.Atom "get-model"]
    --       allLitAssigns <-
    --         forM litPartitions $ \part ->
    --           forM part $ \lit@(Literal (lhs, rhs)) -> do
    --             result <- SMT.getExpr s $ litFun lit
    --             let resultBool =
    --                   case result of
    --                     SMT.Bool b -> b
    --                     SMT.Bits _ v -> v == 1
    --                     x ->
    --                       error $
    --                       "Got bad boolean back from function: " ++ show x
    --             case resultBool of
    --               True -> return $ lhs `Sub` rhs
    --               False -> return $ lhs `NotSub` rhs
    --       --Iterate through our partitions until one fails, or all succeed
    --       findResults i allLitAssigns
    -- findResults i [] =
    --   putStrLn $ "SAT in " ++ show (i + 1) ++ " theory iterations"
    -- findResults i (litAssigns:rest) = do
    --   SMT.simpleCommand s ["push"]
    --   result <- Solver.makePred s options litFun (nonEmptyExpr, litAssigns) --TODO make better name
    --   SMT.simpleCommand s ["pop"]
    --   case result of
    --     Left lemma -> do
    --       SMT.assert s $ makeLemma litFun lemma
    --       solverLoop (i + 1)
    --     Right _ -> findResults i rest
    --   return ()
    -- assertTransitive =
    --   let bitNames = map (\i -> "bit_" ++ show i) [0 .. numBits - 1]
    --       [arg1names, arg2names, arg3names] =
    --         map (\arg -> map (arg ++) bitNames) ["arg1_", "arg2_", "arg3"]
    --       typePairs =
    --         map (\x -> (SMT.Atom x, SMT.tBool)) $
    --         arg1names ++ arg2names ++ arg3names
    --       [arg1, arg2, arg3] =
    --         map (map SMT.Atom) [arg1names, arg2names, arg3names]
    --       bodyCond =
    --         (((Fun "literalValue") $$$ [BitVector arg1, BitVector arg2]) /\
    --          ((Fun "literalValue") $$$ [BitVector arg2, BitVector arg3])) .=>
    --         ((Fun "literalValue") $$$ [BitVector arg1, BitVector arg3])
    --    in SMT.assert s $ fsOr typePairs bodyCond
    -- assertTransitive =
    --   forM
    --     [ (e1, e2, e3)
    --     | e1 <- exprList
    --     , e2 <- exprList
    --     , e3 <- exprList
    --     , length (List.nub [e1, e2, e3]) == 3
    --     ] $ \(e1, e2, e3) -> do
    --     SMT.assert s $
    --       ((exprSubset e1 e2) /\ (exprSubset e2 e3)) .=> (exprSubset e1 e3)
    --Lemmas that always hold, no matter what literals we deal with
    subsetLemmaFor :: Expr -> Expr -> [CExpr]
    --Bottom subset of everything
    subsetLemmaFor Bottom rhs = [Bottom `sub` rhs]
    --Top superset of everything
    subsetLemmaFor lhs Top = [lhs `sub` Top]
    --Assume our lattice is not degenerate
    subsetLemmaFor Top Bottom = [CNot $ Top `sub` Bottom]
    --Everything a subset of itself
    -- subsetLemmaFor lhs rhs
    --   | lhs == rhs = [lhs `sub` rhs]
    -- A subset of A U B
    subsetLemmaFor lhs rhs@(Union e1 e2)
      | lhs `List.elem` [e1, e2] = [lhs `sub` rhs]
      -- A /\ B subset of A
    subsetLemmaFor lhs@(Intersect e1 e2) rhs
      | lhs `List.elem` [e1, e2] = [lhs `sub` rhs]
    --Constant symbols are never in the empty set
    subsetLemmaFor lhs@(FunApp f []) Bottom = [CNot $ lhs `sub` Bottom]
    --Disjoint symbols are never subsets of each otheppr
    subsetLemmaFor lhs@(FunApp f _) rhs@(FunApp g _)
      | f /= g = [CNot $ lhs `sub` rhs]
    subsetLemmaFor _ _ = []
    partitionLiterals :: [[Literal]]
    partitionLiterals = map (rights . (map getLit) . flatten) $ components graph
      where
        litVarEdges =
          [(Right lit, Right lit, map Left (litFreeVars lit)) | lit <- litList]
        varEdges =
          List.nub [(v, v, []) | (_, _, vList) <- litVarEdges, v <- vList]
        (graph, vmap, kmap) = graphFromEdges (litVarEdges ++ varEdges)
        getLit = (\(a, _, _) -> a) . vmap
