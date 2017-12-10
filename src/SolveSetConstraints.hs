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

formulaForCExpr :: (Expr -> BitVector) -> CExpr -> SMT.SExpr
formulaForCExpr exprNum cexp =
  case cexp of
    (s1 `CSubset` s2) -> (Fun "subsetof") $$$ [exprNum s1, exprNum s2]
    (CAnd cexprs) -> andAll $ map self cexprs
    (COr cexprs) -> orAll $ map self cexprs
    (c1 `CImplies` c2) -> self c1 ==> self c2
    (c1 `CIff` c2) -> self c1 === self c2
    (CXor cexprs) -> error "TODO XOR" --"xor" $$ [self c1, self c2]
    (CNot c1) -> SMT.not $ self c1
  where
    self = formulaForCExpr exprNum

makeLemma :: (Expr -> BitVector) -> [Constr] -> SMT.SExpr
makeLemma exprNum clist = SMT.not $ andAll $ map helper clist
  where
    helper c =
      case c of
        e1 `Sub` e2 -> (Fun "subsetof") $$$ [exprNum e1, exprNum e2]
        e1 `NotSub` e2 ->
          SMT.not $ (Fun "subsetof") $$$ [(exprNum e1), (exprNum e2)]
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
  SMT.simpleCommand s ["set-logic", "UF"]
  SMT.simpleCommand s ["push"]
  SMT.declareFun s "subsetof" (litType ++ litType) SMT.tBool
    --Assert the SMT version of our expression
  SMT.assert s $ formulaForCExpr exprFun c
  putStrLn "Starting subset asserts"
  forM [(e1, e2) | e1 <- exprList, e2 <- exprList] $
    uncurry assertSubsetProperty
  putStrLn "Starting transitive assert"
  assertTransitive
  putStrLn "Ending transitive assert"
  solverLoop 0
  where
    exprSubset lhs rhs = (Fun "subsetof") $$$ [exprFun lhs, exprFun rhs]
    nonEmptyConstr = CNot (CSubset nonEmptyExpr Bottom)
    c = (CAnd [cInitial, nonEmptyConstr])
    lits = literalsInCExpr c
    toFloat = (fromIntegral :: Int -> Float)
    numBits = ceiling $ logBase 2 (toFloat $ Set.size exprs)
    litType = replicate numBits SMT.tBool
    exprs = exprsInCExpr c
    exprList = Set.toList exprs
    exprMap = Map.fromList $ zip (Set.toList exprs) [0 ..]
    exprFun = (intToBits numBits) . (exprMap Map.!)
    solverLoop i = do
      putStrLn $ "Solver loop" ++ show i
      result <- SMT.check s
      putStrLn "Check complete"
      case result of
        SMT.Unsat -> putStrLn $ "UNSAT in " ++ show i ++ " theory iterations"
        SMT.Unknown -> error "Shouldn't have quantifiers in solver loop"
        SMT.Sat -> do
          putStrLn "SAT, trying theory solver "
          model <- SMT.command s $ SMT.List [SMT.Atom "get-model"]
          litAssigns <-
            forM (Set.toList lits) $ \(lhs, rhs) -> do
              result <-
                SMT.getExpr s $ (Fun "subsetof") $$$ [exprFun lhs, exprFun rhs]
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
            --putStrLn $ "Outer loop trying: " ++ show litAssigns
          result <- Solver.makePred s options (nonEmptyExpr, litAssigns) --TODO make better name
          SMT.simpleCommand s ["pop"]
          case result of
            Left lemma -> do
              SMT.assert s $ makeLemma exprFun lemma
              solverLoop (i + 1)
            Right _ ->
              putStrLn $ "SAT in " ++ show (i + 1) ++ " theory iterations"
          return ()
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
            (((Fun "subsetof") $$$ [BitVector arg1, BitVector arg2]) /\
             ((Fun "subsetof") $$$ [BitVector arg2, BitVector arg3])) ==>
            ((Fun "subsetof") $$$ [BitVector arg1, BitVector arg3])
      in SMT.assert s $ forAll typePairs bodyCond
    assertSubsetProperty :: Expr -> Expr -> IO ()
      --Bottom subset of everything
    assertSubsetProperty Bottom rhs = SMT.assert s $ exprSubset Bottom rhs
      --Top superset of everything
    assertSubsetProperty lhs Top = SMT.assert s $ exprSubset lhs Top
      --Assume our lattice is not degenerate
    assertSubsetProperty Top Bottom =
      SMT.assert s $ SMT.not $ exprSubset Top Bottom
      --Everything a subset of itself
    assertSubsetProperty lhs rhs
      | lhs == rhs = SMT.assert s $ exprSubset lhs rhs
      -- A subset of A U B
    assertSubsetProperty lhs rhs@(Union e1 e2)
      | lhs `List.elem` [e1, e2] = SMT.assert s $ exprSubset lhs rhs
        -- A /\ B subset of A
    assertSubsetProperty lhs@(Intersect e1 e2) rhs
      | lhs `List.elem` [e1, e2] = SMT.assert s $ exprSubset lhs rhs
      --Constant symbols are never in the empty set
    assertSubsetProperty lhs@(FunApp f []) Bottom =
      SMT.assert s $ SMT.not $ exprSubset lhs Bottom
      --Disjoint symbols are never subsets of each otheppr
    assertSubsetProperty lhs@(FunApp f _) rhs@(FunApp g _)
      | f /= g = SMT.assert s $ SMT.not $ exprSubset lhs rhs
    assertSubsetProperty _ _ = return ()
