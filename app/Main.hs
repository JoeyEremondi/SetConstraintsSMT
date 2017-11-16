module Main where

import qualified SimpleSMT as SMT
import Syntax

main :: IO ()
main = do
  let cset =
        [ (Var "L") `Sub` (FunApp "null" [])
        , (Var "L") `Sub` (FunApp "cons" [Var "L"])
        ]
  l <- SMT.newLogger 0
  s <- SMT.newSolver "z3" ["-in"] (Just l)
  result <- makePred s cset
  putStrLn $ show result
