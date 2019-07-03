{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

module SMTHelpers where

import Syntax

import Control.Monad
import Data.Char (digitToInt)
import qualified Data.List as List
import qualified Z3.Monad as Z3
import ArgParse



data VecFun = VecFun
  { vecFunName :: String
  , arity :: Int
  -- , argUsedBits :: [[Int]]
  , componentFuns :: [Z3.FuncDecl]
  } deriving (Eq, Ord)

instance Show VecFun where
  show = vecFunName

-- arity :: VecFun -> Int
-- arity = length . argUsedBits

-- defineFun s (Fun f) = SMT.defineFun s f

-- declareFun s (Fun f) = SMT.declareFun s f

-- getBitVec :: (Z3.MonadZ3 z3) => BitVector -> IO BitVector
-- getBitVec s bv =
--   forM bv $ \bit -> do
--     v <- SMT.getExpr s bit
--     return $ SMT.value v

-- newtype Fun = Fun
--   { unFun :: String
--   } deriving (Eq, Ord, Show, Read)

newtype BitVector_ a = BitVector
  { bitList :: [a]
  } deriving (Functor, Traversable, Foldable, Eq, Ord)

type BitVector = BitVector_ Z3.AST

-- instance Show BitVector where
--   show (BitVector s) = show $ toDec $ map toBit s
--       -- https://stackoverflow.com/questions/5921573/convert-a-string-representing-a-binary-number-to-a-base-10-string-haskell
--     where
--       toBit (SMT.Atom "true") = '1'
--       toBit (SMT.Atom "false") = '0'
--       toDec :: String -> Int
--       toDec = List.foldl' (\acc x -> acc * 2 + digitToInt x) 0

-- nameToBits :: Int -> String -> BitVector
-- nameToBits nintegral s =
--   BitVector $ [SMT.Atom (s ++ "-" ++ show i) | i <- [0 .. n - 1]]
--   where
--     n = fromIntegral nintegral

-- nameToBitNames :: Int -> String -> [String]
nameToBitNames nintegral s = [(s ++ "-" ++ show i) | i <- [0 .. n - 1]]
  where
    n = fromIntegral nintegral

-- funToBitFuns n f = map Fun $ nameToBitNames n (vecFunName f)

($$) :: (Z3.MonadZ3 z3) => Z3.FuncDecl -> [Z3.AST] -> z3 Z3.AST
($$) = Z3.mkApp
-- ($$) :: Z3.FuncDecl -> [Z3.AST] -> z3 Z3.AST
-- (Fun f) $$ [] = (SMT.Atom f)
-- (Fun f) $$ args = SMT.List (SMT.Atom f : args)

-- ($$$) :: Fun -> [BitVector] -> Z3.AST
-- (Fun f) $$$ args = case concatMap bitList args of
--   [] -> SMT.Atom f
--   l -> SMT.List (SMT.Atom f : l)

--map SMT.List $ List.transpose ((unwrap $ nameToBits n vf) : map unwrap args)
bvApply :: (Z3.MonadZ3 z3) => VecFun -> [BitVector] -> z3 BitVector
bvApply vf args = do
  let argsList = concatMap bitList args
  retBits <- forM (componentFuns vf) $ \ f -> Z3.mkApp f argsList
  return $ BitVector retBits

-- bvMap :: Integral i => i -> Fun -> [BitVector] -> [Z3.AST]
-- bvMap n f args = bvApplyHelper (replicate (fromIntegral n) f) (map unwrap args)
bvApplyHelper fs [] = map ($$ []) fs
bvApplyHelper fs args = map (\x -> (\f x -> f $$ concat x) x args) fs

-- vecEq :: BitVector -> BitVector -> Z3.AST
vecEq (BitVector b1) (BitVector b2) = Z3.mkAnd <$> zipWithM (===) b1 b2

a === b = Z3.mkEq a b

a /\ b = Z3.mkAnd [a,b]

a \/ b = Z3.mkOr [a,b]

a ==> b = Z3.mkImplies a b

--tString = SMT.Atom "String"
--tList t = "List" $$ [t]
-- andAll l =
--   case l of
--     [] -> SMT.bool True
--     [x] -> x
--     _ -> (Fun "and") $$ l

-- --tString = SMT.Atom "String"
-- --tList t = "List" $$ [t]
-- orAll l =
--   case l of
--     [] -> SMT.bool False
--     [x] -> x
--     _ -> (Fun "or") $$ l

-- string s = SMT.Atom $ ['"'] ++ s ++ ['"']
-- slCons h t = "insert" $$ [t, h]
-- sList = foldl slCons (SMT.Atom "nil")
-- applyList f n l = f $$ (map (nthElem l) [0 .. n - 1])
-- nthElem :: Z3.AST -> Int -> Z3.AST
-- nthElem l 0 = "head" $$ [l]
-- nthElem l n = nthElem ("tail" $$ [l]) (n - 1)
-- sshow s =
--   case s of
--     SMT.List [SMT.Atom "_", SMT.Atom ('b':'v':x), _] -> x
--     _ -> SMT.showsSExpr s ""

-- vshow x =
--   case x of
--     SMT.Bits _ i -> show i
--     SMT.Bool b -> show b
--     SMT.Int i -> show i
--     SMT.Other s -> sshow s

-- boolToBit :: Int -> Z3.AST -> Integer -> Z3.AST
-- boolToBit n b shift =
--   (SMT.ite b (SMT.bvShl (SMT.bvBin n 1) (SMT.bvBin n shift)) (SMT.bvBin n 0))

declareVec :: (Z3.MonadZ3 z3) => [Char] -> [Z3.Sort] -> z3 [Z3.AST]
declareVec fullName types =
  forM (zip (nameToBitNames (length types) fullName) types) $ \(nm, t) ->
    Z3.mkFreshVar nm t

declareFunVec ::
     (Z3.MonadZ3 z3, Integral i) => i -> [Char] -> [Z3.Sort] -> [Z3.Sort] -> z3 VecFun
declareFunVec i fullName argTypes retTypes = do
  funDecls <- forM (zip (nameToBitNames (length retTypes) fullName) retTypes) $ \(nm, rtype) ->
          Z3.mkFreshFuncDecl nm argTypes rtype
  return $ VecFun fullName (fromIntegral i) funDecls 


-- forAll :: (Z3.MonadZ3 z3) => [(Z3.AST, Z3.AST)] -> Z3.AST -> z3 Z3.AST
-- forAll typePairs body = SMT.List [SMT.Atom "forall", types, body]
--   where
--     types = SMT.List $ map (\(x, y) -> SMT.List [x, y]) typePairs


-- makeSolver opts = do
--   let vb = verbose opts
--   l <-
--     SMT.newLogger $
--     if vb
--       then 0
--       else 10
--   case (solver opts) of
--     "cvc4-fmf" ->
--       SMT.newSolver
--         "cvc4"
--         ["--lang=smt2", "--incremental", "--fmf-bound", "--mbqi=default"]
--         (Just l)
--     "cvc4" -> SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
--     "boolector" ->
--       SMT.newSolver
--         "boolector"
--         ["--smt2", "--incremental", "--smt2-model"]
--         (Just l)
--     "veriT" ->
--       SMT.newSolver
--         "veriT"
--         [ "--proof-file-from-input"
--         , "--input=smtlib2"
--         , "--output=smtlib2"
--         , "--disable-banner"
--         ]
--         (Just l)
--     _ -> SMT.newSolver "z3" ["-in", "-st", "-v:10"] (Just l)