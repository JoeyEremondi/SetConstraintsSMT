module Main where

import MonadicTheorySolver
import qualified SimpleSMT as SMT
import Syntax
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  let verbose =
        case args of
          (_:"verbose":_) -> True
          _ -> False
  let cset =
        [ (Var "L") `sup` (FunApp "null" [])
        , (Var "L") `sup` (FunApp "cons" [Var "L"])
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
      _ -> SMT.newSolver "z3" ["-in"] (Just l)
  result <- makePred s cset
  putStrLn $ show result
