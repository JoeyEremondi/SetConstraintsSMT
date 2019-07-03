{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module SMTHelpers where

import Syntax

import Control.Monad
import Data.Char (digitToInt)
import qualified Data.List as List
import qualified Data.SBV as SMT
import Data.SBV (SBool, Symbolic, STuple)
import ArgParse



data VecFun = VecFun
  { vecFunName :: String
  , argUsedBits :: [[Int]]
  } deriving (Eq, Ord, Read)

instance Show VecFun where
  show = vecFunName

arity :: VecFun -> Int
arity = length . argUsedBits

-- defineFun s (Fun f) = SMT.defineFun s f

-- declareFun s (Fun f) = SMT.declareFun s f

-- getBitVec :: SMT.Solver -> BitVector -> IO BitVector
-- getBitVec s bv =
--   forM bv $ \bit -> do
--     v <- SMT.getExpr s bit
--     return $ SMT.value v

data Nat = 
  Z | S Nat

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data ENat where
  ENat :: SNat n -> ENat

toENat :: Integer -> ENat
toENat 0 = ENat (SZ)
toENat sn = ENat (SS sn)
  where n = sn - 1
        (ENat en) = toENat n
         

newtype Fun = Fun
  { unFun :: String
  } deriving (Eq, Ord, Show, Read)

data Vec :: * -> Nat -> * where
  VOne :: (SMT.SymVal a) => a -> Vec a Z
  VCpms :: (SMT.SymVal a) => a -> (Vec a n) -> Vec a (S n)
  deriving (Symbolic, Functor, Traversable, Foldable, Eq, Ord)

type BitVector n = Vec SBool n
type FunArgs arity n = Vec (BitVector n) arity
type Constructor arity n = FunArgs arity n -> BitVector n
type InDomain n = (BitVector n) -> SBool

-- instance Show BitVector where
--   show (BitVector s) = show $ toDec $ map toBit s
--       -- https://stackoverflow.com/questions/5921573/convert-a-string-representing-a-binary-number-to-a-base-10-string-haskell
--     where
--       toBit (SMT.Atom "true") = '1'
--       toBit (SMT.Atom "false") = '0'
--       toDec :: String -> Int
--       toDec = List.foldl' (\acc x -> acc * 2 + digitToInt x) 0

-- nameToBits :: Int -> String -> BitVector
nameToBits nintegral s =
  BitVector $ [SMT.Atom (s ++ "-" ++ show i) | i <- [0 .. n - 1]]
  where
    n = fromIntegral nintegral

-- nameToBitNames :: Int -> String -> [String]
nameToBitNames nintegral s = [(s ++ "-" ++ show i) | i <- [0 .. n - 1]]
  where
    n = fromIntegral nintegral

funToBitFuns n f = map Fun $ nameToBitNames n (vecFunName f)

($$) :: Fun -> [SMT.SExpr] -> SMT.SExpr
(Fun f) $$ [] = (SMT.Atom f)
(Fun f) $$ args = SMT.List (SMT.Atom f : args)

($$$) :: Fun -> [BitVector] -> SMT.SExpr
(Fun f) $$$ args = case concatMap bitList args of
  [] -> SMT.Atom f
  l -> SMT.List (SMT.Atom f : l)

--map SMT.List $ List.transpose ((unwrap $ nameToBits n vf) : map unwrap args)
bvApply :: Integral i => i -> VecFun -> [BitVector] -> BitVector
bvApply n vf args =
  BitVector $ bvApplyHelper (funToBitFuns n vf) (map bitList args)

-- bvMap :: Integral i => i -> Fun -> [BitVector] -> [SMT.SExpr]
-- bvMap n f args = bvApplyHelper (replicate (fromIntegral n) f) (map unwrap args)
bvApplyHelper fs [] = map ($$ []) fs
bvApplyHelper fs args = map (\x -> (\f x -> f $$ concat x) x args) fs

vecEq :: BitVector -> BitVector -> SMT.SExpr
vecEq (BitVector b1) (BitVector b2) = andAll $ zipWith SMT.eq b1 b2

(===) = SMT.eq

(/\) = SMT.and

(\/) = SMT.or

(==>) = SMT.implies

--tString = SMT.Atom "String"
--tList t = "List" $$ [t]
andAll l =
  case l of
    [] -> SMT.bool True
    [x] -> x
    _ -> (Fun "and") $$ l

--tString = SMT.Atom "String"
--tList t = "List" $$ [t]
orAll l =
  case l of
    [] -> SMT.bool False
    [x] -> x
    _ -> (Fun "or") $$ l

-- string s = SMT.Atom $ ['"'] ++ s ++ ['"']
-- slCons h t = "insert" $$ [t, h]
-- sList = foldl slCons (SMT.Atom "nil")
-- applyList f n l = f $$ (map (nthElem l) [0 .. n - 1])
-- nthElem :: SMT.SExpr -> Int -> SMT.SExpr
-- nthElem l 0 = "head" $$ [l]
-- nthElem l n = nthElem ("tail" $$ [l]) (n - 1)
sshow s =
  case s of
    SMT.List [SMT.Atom "_", SMT.Atom ('b':'v':x), _] -> x
    _ -> SMT.showsSExpr s ""

vshow x =
  case x of
    SMT.Bits _ i -> show i
    SMT.Bool b -> show b
    SMT.Int i -> show i
    SMT.Other s -> sshow s

boolToBit :: Int -> SMT.SExpr -> Integer -> SMT.SExpr
boolToBit n b shift =
  (SMT.ite b (SMT.bvShl (SMT.bvBin n 1) (SMT.bvBin n shift)) (SMT.bvBin n 0))

declareVec :: SMT.Solver -> [Char] -> [SMT.SExpr] -> IO [SMT.SExpr]
declareVec s fullName types =
  forM (zip (nameToBitNames (length types) fullName) types) $ \(nm, t) ->
    SMT.declare s nm t

declareFunVec ::
     SMT.Solver -> [Char] -> [SMT.SExpr] -> [SMT.SExpr] -> IO [SMT.SExpr]
declareFunVec s fullName argTypes retTypes =
  forM (zip (nameToBitNames (length retTypes) fullName) retTypes) $ \(nm, rtype) ->
    SMT.declareFun s nm argTypes rtype

defineFunVec = error "TODO"

forAll :: [(SMT.SExpr, SMT.SExpr)] -> SMT.SExpr -> SMT.SExpr
forAll typePairs body = SMT.List [SMT.Atom "forall", types, body]
  where
    types = SMT.List $ map (\(x, y) -> SMT.List [x, y]) typePairs


makeSolver opts = do
  let vb = verbose opts
  l <-
    SMT.newLogger $
    if vb
      then 0
      else 10
  case (solver opts) of
    "cvc4-fmf" ->
      SMT.newSolver
        "cvc4"
        ["--lang=smt2", "--incremental", "--fmf-bound", "--mbqi=default"]
        (Just l)
    "cvc4" -> SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
    "boolector" ->
      SMT.newSolver
        "boolector"
        ["--smt2", "--incremental", "--smt2-model"]
        (Just l)
    "veriT" ->
      SMT.newSolver
        "veriT"
        [ "--proof-file-from-input"
        , "--input=smtlib2"
        , "--output=smtlib2"
        , "--disable-banner"
        ]
        (Just l)
    _ -> SMT.newSolver "z3" ["-in", "-st", "-v:10"] (Just l)