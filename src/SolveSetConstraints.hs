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
import qualified SimpleSMT as SMT
import Syntax

import Data.Either (rights)
import Data.Graph
import Data.Tree (flatten)
import Data.Tuple (swap)
import Debug.Trace (trace)

formulaForCExpr :: (Literal -> SMT.SExpr) -> CExpr -> SMT.SExpr
formulaForCExpr litNum cexp =
  case cexp of
    (s1 `CSubset` s2) -> litNum $ Literal (s1, s2)
    (CAnd cexprs) -> andAll $ map self cexprs
    (COr cexprs) -> orAll $ map self cexprs
    (c1 `CImplies` c2) -> self c1 ==> self c2
    (c1 `CIff` c2) -> self c1 === self c2
    (CXor cexprs) -> error "TODO XOR" --"xor" $$ [self c1, self c2]
    (CNot c1) -> SMT.not $ self c1
  where
    self = formulaForCExpr litNum

makeLemma :: (Literal -> SMT.SExpr) -> [Constr] -> SMT.SExpr
makeLemma litNum clist = SMT.not $ andAll $ map helper clist
  where
    helper c =
      case c of
        e1 `Sub` e2 -> litNum $ Literal (e1, e2)
        e1 `NotSub` e2 -> SMT.not $ litNum $ Literal (e1, e2)

--intToBits :: Integral i => i -> String
intToBits n i = BitVector $ map bitToSexp paddedBinaryString
  where
    asBinaryString = showIntAtBase 2 intToDigit i ""
    paddedBinaryString =
      reverse $ take n $ (reverse asBinaryString) ++ repeat '0'
    bitToSexp '0' = SMT.bool False
    bitToSexp '1' = SMT.bool True

solveSetConstraints :: SMT.Solver -> Options -> (Expr, CExpr) -> IO ()
solveSetConstraints s options (nonEmptyExpr, cInitial)
  --Declare our inclusion function
  --
 = do
  putStrLn $ "cInitial: " ++ show cInitial
  SMT.simpleCommand s ["set-logic", "UF"]
  SMT.simpleCommand s ["set-option", ":smt.mbqi", "true"]
  SMT.simpleCommand s ["push"]
  -- SMT.declareFun s "literalValue" litType SMT.tBool
  forM literalNames $ \(SMT.Atom ln) -> SMT.declare s ln SMT.tBool
  --Assert the SMT version of our expression
  SMT.assert s $ formulaForCExpr litFun c
  putStrLn $
    "Done asserting formula, " ++
    show (Set.size baseLits) ++
    " base literals, " ++ show (Set.size lits) ++ " literals total"
  putStrLn $
    "Partitioned into " ++
    show (length litPartitions) ++ " subproblems: " ++ show (litPartitions)
  -- forM [(e1, e2) | e1 <- exprList, e2 <- exprList] $
  --   uncurry subsetLemmaFor
  putStrLn "Done asserting subset properties"
  -- assertTransitive
  putStrLn "Done asserting transitivity"
  solverLoop 0
    -- exprSubset lhs rhs = (Fun "literalValue") $$$ [exprFun lhs, exprFun rhs]
  where
    nonEmptyConstr = CNot (CSubset nonEmptyExpr Bottom)
    cBase = (CAnd [cInitial, nonEmptyConstr])
    cStructural =
      CAnd $
      concatMap
        (uncurry subsetLemmaFor)
        [(e1, e2) | e1 <- baseExprList, e2 <- baseExprList]
    cInter = CAnd [cBase, cStructural] --This should have all the literals we need
    cTransitive =
      CAnd
        [ transConstr e1 e2 e3
        | Literal (e1, e2) <- litList
        , Just e3list <- [Map.lookup e2 litRightSidesMap]
        , e3 <- e3list
        , Map.member (Literal (e1, e3)) litMap
        ]
      where
        transConstr e1 e2 e3 =
          (CAnd [CSubset e1 e2, CSubset e2 e3]) `CImplies` (CSubset e1 e3)
    c = CAnd [cInter, cTransitive] --TODO add more
    literalNames =
      map (\i -> SMT.Atom $ "literal_" ++ show i) [0 .. length lits - 1]
    baseLits = literalsInCExpr cBase
    lits = literalsInCExpr cInter
    litList = Set.toList lits
    litMap = Map.fromList $ flip zip literalNames $ litList
    litFun l =
      case (Map.lookup l litMap) of
        Nothing -> error ("Key" ++ show l ++ " not in map " ++ show litMap)
        Just x -> x
    litRightSidesMap =
      Map.fromList
        [ (e1, [e2 | Literal (e1', e2) <- litList, e1' == e1])
        | Literal (e1, _) <- litList
        ]
    litPartitions = partitionLiterals
    toFloat = (fromIntegral :: Int -> Float)
    numBits = ceiling $ logBase 2 (toFloat $ Set.size lits)
    litType = replicate numBits SMT.tBool
    baseExprs = exprsInCExpr cBase
    baseExprList = Set.toList baseExprs
    exprs = exprsInCExpr cInter
    exprList = Set.toList exprs
    -- exprMap = Map.fromList $ zip (exprList) [0 ..]
    -- exprFun = (intToBits numBits) . (exprMap Map.!)
    solverLoop i = do
      putStrLn $ "SolverLoop" ++ show i
      result <- SMT.check s
      case result of
        SMT.Unsat -> putStrLn $ "UNSAT in " ++ show i ++ " theory iterations"
        SMT.Unknown -> error "Shouldn't have quantifiers in solver loop"
        SMT.Sat -> do
          putStrLn "Solver loop SAT, trying theory solver"
          model <- SMT.command s $ SMT.List [SMT.Atom "get-model"]
          allLitAssigns <-
            forM litPartitions $ \part ->
              forM part $ \lit@(Literal (lhs, rhs)) -> do
                result <- SMT.getExpr s $ litFun lit
                let resultBool =
                      case result of
                        SMT.Bool b -> b
                        SMT.Bits _ v -> v == 1
                        x ->
                          error $
                          "Got bad boolean back from function: " ++ show x
                case resultBool of
                  True -> return $ lhs `Sub` rhs
                  False -> return $ lhs `NotSub` rhs
          --Iterate through our partitions until one fails, or all succeed
          findResults i allLitAssigns
    findResults i [] =
      putStrLn $ "SAT in " ++ show (i + 1) ++ " theory iterations"
    findResults i (litAssigns:rest) = do
      SMT.simpleCommand s ["push"]
      result <- Solver.makePred s options (nonEmptyExpr, litAssigns) --TODO make better name
      SMT.simpleCommand s ["pop"]
      case result of
        Left lemma -> do
          SMT.assert s $ makeLemma litFun lemma
          solverLoop (i + 1)
        Right _ -> findResults i rest
      return ()
    assertTransitive =
      let bitNames = map (\i -> "bit_" ++ show i) [0 .. numBits - 1]
          [arg1names, arg2names, arg3names] =
            map (\arg -> map (arg ++) bitNames) ["arg1_", "arg2_", "arg3"]
          typePairs =
            map (\x -> (SMT.Atom x, SMT.tBool)) $
            arg1names ++ arg2names ++ arg3names
          [arg1, arg2, arg3] =
            map (map SMT.Atom) [arg1names, arg2names, arg3names]
          bodyCond =
            (((Fun "literalValue") $$$ [BitVector arg1, BitVector arg2]) /\
             ((Fun "literalValue") $$$ [BitVector arg2, BitVector arg3])) ==>
            ((Fun "literalValue") $$$ [BitVector arg1, BitVector arg3])
      in SMT.assert s $ forAll typePairs bodyCond
    -- assertTransitive =
    --   forM
    --     [ (e1, e2, e3)
    --     | e1 <- exprList
    --     , e2 <- exprList
    --     , e3 <- exprList
    --     , length (List.nub [e1, e2, e3]) == 3
    --     ] $ \(e1, e2, e3) -> do
    --     SMT.assert s $
    --       ((exprSubset e1 e2) /\ (exprSubset e2 e3)) ==> (exprSubset e1 e3)
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
