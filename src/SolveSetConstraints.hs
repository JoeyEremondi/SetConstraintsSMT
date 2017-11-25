module SolveSetConstraints where

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified MonadicTheorySolver as Solver
import SMTHelpers
import qualified SimpleSMT as SMT
import Syntax

formulaForCExpr :: (Expr -> SMT.SExpr) -> CExpr -> SMT.SExpr
formulaForCExpr exprNum cexp =
  case cexp of
    (s1 `CSubset` s2) -> (Fun "subsetof") $$ [exprNum s1, exprNum s2]
    (CAnd cexprs) -> andAll $ map self cexprs
    (COr cexprs) -> orAll $ map self cexprs
    (c1 `CImplies` c2) -> self c1 ==> self c2
    (c1 `CIff` c2) -> self c1 === self c2
    (CXor cexprs) -> error "TODO XOR" --"xor" $$ [self c1, self c2]
    (CNot c1) -> SMT.not $ self c1
  where
    self = formulaForCExpr exprNum

makeLemma :: (Expr -> SMT.SExpr) -> [Constr] -> SMT.SExpr
makeLemma exprNum clist = SMT.not $ andAll $ map helper clist
  where
    helper c =
      case c of
        e1 `Sub` e2 -> (Fun "subsetof") $$ [exprNum e1, exprNum e2]
        e1 `NotSub` e2 -> SMT.not $ (Fun "subsetof") $$ [exprNum e1, exprNum e2]

solveSetConstraints :: SMT.Solver -> CExpr -> IO ()
solveSetConstraints s c
  --Declare our inclusion function
  --
 = do
  SMT.simpleCommand s ["set-logic", "UFBV"]
  SMT.simpleCommand s ["push"]
  SMT.declareFun s "subsetof" [litType, litType] SMT.tBool
  --Assert the SMT version of our expression
  SMT.assert s $ formulaForCExpr exprFun c
  solverLoop
  where
    lits = literalsInCExpr c
    toFloat = (fromIntegral :: Int -> Float)
    numBits = ceiling $ logBase 2 (toFloat $ Set.size lits)
    litType = SMT.tBits numBits
    exprs = exprsInCExpr c
    exprMap = Map.fromList $ zip (Set.toList exprs) [0 ..]
    exprFun = (SMT.bvBin $ fromIntegral numBits) . (exprMap Map.!)
    solverLoop = do
      result <- SMT.check s
      case result of
        SMT.Unsat -> putStrLn "UNSATISFIABLE"
        SMT.Unknown -> error "Shouldn't have quantifiers in solver loop"
        SMT.Sat -> do
          model <- SMT.command s $ SMT.List [SMT.Atom "get-model"]
          litAssigns <-
            forM (Set.toList lits) $ \(lhs, rhs) -> do
              result <-
                SMT.getExpr s $ (Fun "subsetof") $$ [exprFun lhs, exprFun rhs]
              let resultBool =
                    case result of
                      SMT.Bool b -> b
                      SMT.Bits _ v -> v == 1
                      x ->
                        error $ "Got bad boolean back from function: " ++ show x
              case resultBool of
                True -> return $ lhs `Sub` rhs
                False -> return $ lhs `NotSub` rhs
          SMT.simpleCommand s ["push"]
          result <- Solver.makePred s litAssigns --TODO make better name
          SMT.simpleCommand s ["pop"]
          case result of
            Left lemma -> do
              SMT.assert s $ makeLemma exprFun lemma
              solverLoop
            Right _ -> putStrLn "SAT"
          return ()
      return ()
