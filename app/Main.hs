module Main where

import qualified SimpleSMT as SMT
import Syntax
import System.Environment

import SolveSetConstraints

zero = VecFun "zero"

ssucc = VecFun "succ"

_Null = FunApp (VecFun "Null") []

_Cons h t = FunApp (VecFun "Cons") [h, t]

_X = Var "X"

_D = Var "D"

_C1 = Var "C1"

_C2 = Var "C2"

_Y = FunApp (VecFun "Const") []

main :: IO ()
main = do
  args <- getArgs
  let verbose =
        case args of
          (_:"verbose":_) -> True
          _ -> False
  -- let cset =
  --       CAnd
  --         [ ((Var "N") `sup` ((FunApp zero [])))
  --         , ((Var "N") `sup` ((FunApp ssucc [Var "N"])))
  --         , ((Var "L") `eq`
  --            ((FunApp listNull []) `Union` ((FunApp ccons [Var "N", Var "L"]))))
  --         ]
  let goodCheck =
        CAnd
          [ _D `sub` _Cons Top Top
          , _X `sub` ((_Cons Top Top) `Union` _Null)
          , _X `notsub` _Cons Top Top
          , ((_Null `Intersect` _X) `notsub` Bottom) `CImplies` (_C1 `eq` _Null)
          , ((_Null `Intersect` _X) `eq` Bottom) `CImplies` (_C1 `eq` Bottom)
          , ((_Null `Intersect` _Cons Top Top) `notsub` Bottom) `CImplies`
            (_C2 `eq` _Cons _Y (_Cons _Y _D))
          , ((_Null `Intersect` _Cons Top Top) `eq` Bottom) `CImplies`
            (_C2 `eq` Bottom)
          , _D `eq` (_C1 `Union` _C2)
          ]
    -- D < Cons(T,T),
    -- X /< Cons(T,T)
    -- Null /\ X /< {} => C1 == Null
    -- Null /\ X = {} => C1 == {}
    -- Cons(T,T) /\ X /< {} => C2 = Cons(A, Cons(A, D))  
    -- Cons(T,T) /\ X == {} => C2 = {}
    -- D = C1 \/ C2
  let badCheck = CAnd []
  l <-
    SMT.newLogger $
    if verbose
      then 0
      else 10
  s <-
    case args of
      "cvc4-fmf":_ ->
        SMT.newSolver
          "cvc4"
          ["--lang=smt2", "--incremental", "--fmf-bound", "--mbqi=default"]
          (Just l)
      "cvc4":_ -> SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
      "boolector":_ ->
        SMT.newSolver
          "boolector"
          ["--smt2", "--incremental", "--smt2-model"]
          (Just l)
      "veriT":_ ->
        SMT.newSolver
          "veriT"
          [ "--proof-file-from-input"
          , "--input=smtlib2"
          , "--output=smtlib2"
          , "--disable-banner"
          ]
          (Just l)
      _ -> SMT.newSolver "z3" ["-in"] (Just l)
  solveSetConstraints s goodCheck
  -- putStrLn $ show result
