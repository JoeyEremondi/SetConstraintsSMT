module Main where

import qualified SimpleSMT as SMT
import Syntax
import System.Environment

import SolveSetConstraints

zero = VecFun "zero"

ssucc = VecFun "succ"

listNull = VecFun "listNull"

ccons = VecFun "ccons"

main :: IO ()
main = do
  args <- getArgs
  let verbose =
        case args of
          (_:"verbose":_) -> True
          _ -> False
  let cset =
        CAnd
          [ ((Var "N") `eq` ((FunApp zero []) `Union` (FunApp ssucc [Var "N"])))
          , ((Var "L") `eq`
             ((FunApp listNull []) `Union` ((FunApp ccons [Var "N", Var "L"]))))
          --, 
          ]
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
