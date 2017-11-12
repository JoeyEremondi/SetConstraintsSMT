module Main where

import qualified SimpleSMT as SMT
import Syntax

main :: IO ()
main = do
  let cset = [(Var "L") `Sub` (Var "L" `Union` Var "L")]
  l <- SMT.newLogger 0
  s <- SMT.newSolver "cvc4" ["--lang=smt2"] (Just l)
  makePred s cset
  print =<< SMT.check s
  print =<< SMT.getExprs s []
