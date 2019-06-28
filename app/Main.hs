{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Andersen
import qualified SimpleSMT as SMT
import Syntax
import System.Environment

import ArgParse
import Data.Semigroup
import Options.Applicative
import SolveSetConstraints 
import SMTHelpers (makeSolver) 

zero = "zero"

ssucc = "succ"

_Null = FunApp ("Null") []

_Cons h t = FunApp ("Cons") [h, t]

_X = Var "X"

_D = Var "D"

_C1 = Var "C1"

_C2 = Var "C2"

_Y = FunApp ("Const") []

main :: IO ()
main = do
  let theInfo =
        info
          (sample <**> helper)
          (fullDesc <> progDesc "Print a greeting for TARGET" <>
           header "hello - a test for optparse-applicative")
  options <- execParser theInfo
  -- let cset = 
  --       CAnd
  --         [ ((Var "N") `sup` ((FunApp zero [])))
  --         , ((Var "N") `sup` ((FunApp ssucc [Var "N"])))
  --         -- , ((Var "L") `eq`
  --         --    ((FunApp listNull []) `Union` ((FunApp ccons [Var "N", Var "L"]))))
  --         ]
  -- let goodCheck =
  --       CAnd
  --         [ _D `sub` _Cons Top Top
  --         , _X `sub` ((_Cons Top Top) `Union` _Null)
  --         , _X `notsub` _Cons Top Top
  --         , ((_Null `Intersect` _X) `notsub` Bottom) `CImplies` (_C1 `eq` _Null)
  --         , ((_Null `Intersect` _X) `eq` Bottom) `CImplies` (_C1 `eq` Bottom)
  --         , ((_Null `Intersect` _Cons Top Top) `notsub` Bottom) `CImplies`
  --           (_C2 `eq` _Cons _Y (_Cons _Y _D))
  --         , ((_Null `Intersect` _Cons Top Top) `eq` Bottom) `CImplies`
  --           (_C2 `eq` Bottom)
  --         , _D `eq` (_C1 `Union` _C2)
  --         ]
    -- D < Cons(T,T),
    -- X /< Cons(T,T)
    -- Null /\ X /< {} => C1 == Null
    -- Null /\ X = {} => C1 == {}
    -- Cons(T,T) /\ X /< {} => C2 = Cons(A, Cons(A, D))  
    -- Cons(T,T) /\ X == {} => C2 = {}
    -- D = C1 \/ C2
  inConstrsString <- readFile (inFile options)
  let (inConstrs@(e,c) :: (Expr, CExpr)) =
        case parseBanshee options of
          False -> read inConstrsString
          True -> (Var "XDummy", parseBansheeString inConstrsString)
  let constr = CAnd [c, (CNot (e `CSubset` Bottom))]
  s <- makeSolver options
  -- solveSetConstraints s1 cset
  -- solveSetConstraints s1 goodCheck
  eitherRet <- solveSetConstraints s options constr
  case eitherRet of
    Left s -> putStrLn (";;;; " ++ s)
    Right _ -> putStrLn ";;;; Solution found"
  -- putStrLn $ show result


