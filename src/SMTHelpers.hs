{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module SMTHelpers where

import Syntax

import Control.Monad
import Data.Char (digitToInt)
import qualified Data.List as List
import qualified SimpleSMT as SMT

defineFun s (Fun f) = SMT.defineFun s f

declareFun s (Fun f) = SMT.declareFun s f

getBitVec :: SMT.Solver -> BitVector -> IO BitVector
getBitVec s bv = do
  resultBits <-
    forM (bv) $ \bit -> do
      v <- SMT.getExpr s bit
      return $ SMT.value v
  return resultBits

newtype Fun = Fun
  { unFun :: String
  } deriving (Eq, Ord, Show, Read)

newtype BitVector_ a = BitVector
  { unwrap :: [a]
  } deriving (Functor, Traversable, Foldable, Eq, Ord)

type BitVector = BitVector_ SMT.SExpr

instance Show BitVector where
  show (BitVector s) = show $ toDec $ map toBit s
      -- https://stackoverflow.com/questions/5921573/convert-a-string-representing-a-binary-number-to-a-base-10-string-haskell
    where
      toBit (SMT.Atom "true") = '1'
      toBit (SMT.Atom "false") = '0'
      toDec :: String -> Int
      toDec = List.foldl' (\acc x -> acc * 2 + digitToInt x) 0

-- nameToBits :: Int -> String -> BitVector
nameToBits nintegral s =
  BitVector $ [SMT.Atom (s ++ "-" ++ show i) | i <- [0 .. n - 1]]
  where
    n = fromIntegral nintegral

-- nameToBitNames :: Int -> String -> [String]
nameToBitNames nintegral s = [(s ++ "-" ++ show i) | i <- [0 .. n - 1]]
  where
    n = fromIntegral nintegral

funToBitFuns n (VecFun f) = map Fun $ nameToBitNames n f

($$) :: Fun -> [SMT.SExpr] -> SMT.SExpr
(Fun f) $$ [] = (SMT.Atom f)
(Fun f) $$ args = SMT.List (SMT.Atom f : args)

--map SMT.List $ List.transpose ((unwrap $ nameToBits n vf) : map unwrap args)
bvApply :: Integral i => i -> VecFun -> [BitVector] -> BitVector
bvApply n vf args =
  BitVector $ bvApplyHelper (funToBitFuns n vf) (map unwrap args)

-- bvMap :: Integral i => i -> Fun -> [BitVector] -> [SMT.SExpr]
-- bvMap n f args = bvApplyHelper (replicate (fromIntegral n) f) (map unwrap args)
bvApplyHelper fs [] = map ($$ []) fs
bvApplyHelper fs args = zipWith (\f x -> f $$ concat x) fs (repeat args)

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

declareVec s fullName types =
  forM (zip (nameToBitNames (length types) fullName) types) $ \(nm, t) ->
    SMT.declare s nm t

declareFunVec s fullName argTypes retTypes =
  forM (zip (nameToBitNames (length retTypes) fullName) retTypes) $ \(nm, rtype) ->
    SMT.declareFun s nm argTypes rtype

defineFunVec = error "TODO"
