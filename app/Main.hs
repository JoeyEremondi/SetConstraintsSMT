module Main where

import qualified SimpleSMT as SMT
import Syntax
import System.Environment

import SolveSetConstraints

main :: IO ()
main = do
  args <- getArgs
  let verbose =
        case args of
          (_:"verbose":_) -> True
          _ -> False
  let cset =
        ((Var "N") `sup` (FunApp "zero" [])) `CAnd`
        ((Var "N") `sup` (FunApp "succ" [Var "N"])) `CAnd`
        ((Var "L") `sup` (FunApp "null" [])) `CAnd`
        ((Var "L") `sup` (FunApp "cons" [Var "N", Var "L"]))
  l <-
    SMT.newLogger $
    if verbose
      then 0
      else 10
  s <-
    case args of
      "cvc4":_ ->
        SMT.newSolver
          "cvc4"
          ["--lang=smt2", "--fmf-bound", "--incremental"]
          (Just l)
      "boolector":_ ->
        SMT.newSolver
          "boolector"
          ["--smt2", "--incremental", "--smt2-model"]
          (Just l)
      _ -> SMT.newSolver "z3" ["-in"] (Just l)
  solveSetConstraints s cset
  -- putStrLn $ show result
