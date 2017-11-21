module SolveSetConstraints where

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified MonadicTheorySolver as Solver
import SMTHelpers
import qualified SimpleSMT as SMT
import Syntax

litType = SMT.tInt

formulaForCExpr :: (Expr -> SMT.SExpr) -> CExpr -> SMT.SExpr
formulaForCExpr exprNum cexp =
  case cexp of
    (s1 `CSubset` s2) -> "subsetof" $$ [exprNum s1, exprNum s2]
    (c1 `CAnd` c2) -> self c1 /\ self c2
    (c1 `COr` c2) -> self c1 \/ self c2
    (c1 `CImplies` c2) -> self c1 ==> self c2
    (c1 `CIff` c2) -> self c1 === self c2
    (c1 `CXor` c2) -> "xor" $$ [self c1, self c2]
    (CNot c1) -> SMT.not $ self c1
  where
    self = formulaForCExpr exprNum

makeLemma :: (Expr -> SMT.SExpr) -> [Constr] -> SMT.SExpr
makeLemma exprNum clist = SMT.not $ andAll $ map helper clist
  where
    helper c =
      case c of
        e1 `Sub` e2 -> "subsetof" $$ [exprNum e1, exprNum e2]
        e1 `NotSub` e2 -> SMT.not $ "subsetof" $$ [exprNum e1, exprNum e2]

solveSetConstraints :: SMT.Solver -> CExpr -> IO ()
solveSetConstraints s c
  --Declare our inclusion function
 = do
  SMT.declareFun s "subsetof" [SMT.tInt, SMT.tInt] SMT.tBool
  --Assert the SMT version of our expression
  SMT.assert s $ formulaForCExpr exprFun c
  solverLoop
  where
    lits = literalsInCExpr c
    exprs = exprsInCExpr c
    exprMap = Map.fromList $ zip (Set.toList exprs) [0 ..]
    exprFun = SMT.int . (exprMap Map.!)
    solverLoop = do
      result <- SMT.check s
      case result of
        SMT.Unsat -> putStrLn "UNSATISFIABLE"
        SMT.Unknown -> error "Shouldn't have quantifiers in solver loop"
        SMT.Sat -> do
          model <- SMT.command s $ SMT.List [SMT.Atom "get-model"]
          litAssigns <-
            forM (Set.toList lits) $ \(lhs, rhs) -> do
              result <- SMT.getExpr s $ "subsetof" $$ [exprFun lhs, exprFun rhs]
              case result of
                SMT.Bool True -> return $ lhs `Sub` rhs
                SMT.Bool False -> return $ lhs `NotSub` rhs
          result <- Solver.makePred s litAssigns --TODO make better name
          case result of
            Left lemma -> do
              SMT.assert s $ makeLemma exprFun lemma
              solverLoop
            Right _ -> putStrLn "SAT"
          return ()
      return ()
