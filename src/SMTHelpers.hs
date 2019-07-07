{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-} 
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveDataTypeable #-}

module SMTHelpers where

import Syntax

import Data.Data (Proxy(..))

import Control.Monad
import Data.Char (digitToInt)
import qualified Data.List as List
import Ersatz
import ArgParse

import Data.Data (Data)


import Data.Constraint (Dict(..))


-- data VecFun = VecFun
--   { vecFunName :: String
--   , argUsedBits :: [[Int]]
--   } deriving (Eq, Ord, Read)

-- instance Show VecFun where
--   show = vecFunName

-- arity :: VecFun -> Int
-- arity = length . argUsedBits

-- defineFun s (Fun f) = SBV.defineFun s f

-- declareFun s (FuadeclareFun s f

-- getBitVec :: SMTaBitVector -> IO BitVector
-- getBitVec s bv =a_
--   forM bv $ \bit -> do
--     v <- SBV.getExpr s bit
--     return $ SBV.value v

data Nat = 
  Z | S Nat

-- type DictForAll n = forall a . SymVal a => Dict (SymVal (Vec a n))



data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n ->  SNat (S n)

-- buildInst :: forall n . DictForAll n -> DictForAll (S n)
-- buildInst d = result
--   where
--     result :: forall a' . SymVal a' => Dict (SymVal (Vec a' (S n)))
--     result = case (d @a') of
--       Dict -> Dict

-- getInst :: forall n . SNat n -> DictForAll n
-- getInst sz@SZ = Dict
-- getInst ss@(SS pred d) = 
--   let 
--     result :: forall a' . SymVal a' => Dict (SymVal (Vec a' n))
--     result = case pred of
--       (_ :: SNat npred) -> case d @a' of
--         Dict -> Dict
--   in 
--     result 



sNatToInt :: forall n . SNat n -> Int
sNatToInt sn = helper sn 0
  where 
    helper :: forall n . SNat n -> Int -> Int
    helper SZ i = i
    helper ssn@(SS sn) i =
      case ssn of
        (_ :: SNat (S n')) -> 
          helper @n' sn (1+i)

data ENat where
  ENat :: SNat n -> ENat

eSucc :: ENat -> ENat
eSucc (ENat SZ) = ENat (SS SZ) 
eSucc (ENat ss@(SS pred)) = case pred of
  (_ :: SNat nfoo) -> ENat (SS ss)
    

toENat :: Int -> ENat
toENat 0 = ENat (SZ)
toENat sn = eSucc (toENat n)
  where n = sn - 1
        -- (ENat (en :: SNat n))  = toENat n
         

newtype Fun = Fun
  { unFun :: String
  } deriving (Eq, Ord, Show, Read)


data Vec :: * -> Nat -> * where
  VNil :: Vec a Z
  VCons :: a -> Vec a n -> Vec a (S n)
  -- deriving (Read, Data, Show, SBV.HasKind, SymVal)

  -- deriving (Read, Data, Show, SBV.HasKind, SymVal)


-- type SVec a n = SBV (Vec a n)


-- vecInstance :: forall a (n :: Nat) . (SymVal a) => SNat n -> Dict (SymVal (Vec a n))
-- vecInstance sz@SZ = 
--   case sz of
--     (_ :: SNat Z) -> Dict
-- vecInstance ss@(SS n) = 
--   case ss of
--     (_ :: SNat (S n')) -> 
--       case vecInstance @a @n' n of
--         Dict -> Dict 

makeSVec :: forall a (n :: Nat) .  SNat n -> [a] -> Vec a n
makeSVec sz@SZ [] = 
  case sz of
    (_ :: SNat Z) -> VNil
makeSVec ss@(SS npred) (first:rest) = --trace ("Making vec length " ++ show (sNatToInt ss) ++ " from" ++ show (first:rest)) $ 
  case ss of
    (_ :: SNat (S n')) -> 
      case (makeSVec @a @n' npred rest  ) of
        (vecRest) -> VCons first vecRest 
-- makeSVec sn l = error $ "Can't make vector of length" ++ show (sNatToInt  sn) ++ " from list of length " ++ show l

type BitVector n = Vec Bit n 
type FunArgs arity n = Vec (BitVector n) arity
type Constructor arity n = FunArgs arity n -> BitVector n
type InDomain n = (BitVector n) -> Bit

data VecFun :: Nat -> * where
  VecFun :: forall arity n . String -> SNat arity -> Constructor arity n -> VecFun n

arity (VecFun _ sn _) = sNatToInt sn
vecFunName (VecFun name _ _) = name

genVec :: (Monad m) => (m a) -> SNat n -> m (Vec a n)
genVec gen sz@SZ = return VNil
genVec gen ss@(SS spred) = do
  tail <- genVec gen spred
  head <- gen
  return $ VCons head tail

ithElem :: forall a n .  Int -> Vec a n -> SNat n -> a
-- ithElem 0 bv sz@SZ  = 
--   case sz of
--     (_ :: SNat Z) -> bv
ithElem i  (VCons h t) ss@(SS spred) = 
  case ss of
    (_ :: SNat (S npred)) -> 
      case (i) of
          (0) -> h
          (_) -> ithElem (i-1)  t spred 
ithElem i bv sz = error $ "iThelem" ++ show (i, sNatToInt sz)

vecToList :: forall a n . Vec a n -> SNat n -> [a]
vecToList VNil sz@SZ  = 
  case sz of
    (_ :: SNat Z) -> []
vecToList (VCons h t) ss@(SS spred) = 
  case ss of
    (_ :: SNat (S npred)) -> h : vecToList t spred 
-- ithElem i (BitVector x) n = _ -- x !!! (fromInteger i)

existsBitVec :: (Monad m) =>  SNat n -> m (BitVector n)
existsBitVec = genVec _

forallBitVec :: (Monad m) =>  SNat n -> m (BitVector n)
forallBitVec = genVec _

-- 
type One = S Z

sOne :: SNat One
sOne = SS SZ

    
-- makeBitVector :: [Bit] -> EBitVector 
-- makeBitVector [e] = EBitVector $ (BitVector e :: BitVector Z)
-- makeBitVector (first : rest) = EBitVector $ BitVector (first, bvRest)
--   where (EBitVector bvRest) = makeBitVector rest

-- instance Show BitVector where
--   show (BitVector s) = show $ toDec $ map toBit s
--       -- https://stackoverflow.com/questions/5921573/convert-a-string-representing-a-binary-number-to-a-base-10-string-haskell
--     where
--       toBit (SBV.Atom "true") = '1'
--       toBit (SBV.Atom "false") = '0'
--       toDec :: String -> Int
--       toDec = List.foldl' (\acc x -> acc * 2 + digitToInt x) 0






-- declareVec :: SBV.Solver -> [Char] -> [SBV.SExpr] -> IO [SBV.SExpr]
-- declareVec s fullName types =
--   forM (zip (nameToBitNames (length types) fullName) types) $ \(nm, t) ->
--     SBV.declare s nm t

-- declareFunVec ::
--      SBV.Solver -> [Char] -> [SBV.SExpr] -> [SBV.SExpr] -> IO [SBV.SExpr]
-- declareFunVec s fullName argTypes retTypes =
--   forM (zip (nameToBitNames (length retTypes) fullName) retTypes) $ \(nm, rtype) ->
--     SBV.declareFun s nm argTypes rtype

-- defineFunVec = error "TODO"

-- forAll :: [(SBV.SExpr, SBV.SExpr)] -> SBV.SExpr -> SBV.SExpr
-- forAll typePairs body = SBV.List [SBV.Atom "forall", types, body]
--   where
--     types = SBV.List $ map (\(x, y) -> SBV.List [x, y]) typePairs


-- makeSolver opts = do
--   let vb = verbose opts
--   l <-
--     SBV.newLogger $
--     if vb
--       then 0
--       else 10
--   case (solver opts) of
--     "cvc4-fmf" ->
--       SBV.newSolver
--         "cvc4"
--         ["--lang=smt2", "--incremental", "--fmf-bound", "--mbqi=default"]
--         (Just l)
--     "cvc4" -> SBV.newSolver "cvc4" ["--lang=smt2", "--incremental"] (Just l)
--     "boolector" ->
--       SBV.newSolver
--         "boolector"
--         ["--smt2", "--incremental", "--smt2-model"]
--         (Just l)
--     "veriT" ->
--       SBV.newSolver
--         "veriT"
--         [ "--proof-file-from-input"
--         , "--input=smtlib2"
--         , "--output=smtlib2"
--         , "--disable-banner"
--         ]
--         (Just l)
--     _ -> SBV.newSolver "z3" ["-in", "-st", "-v:10"] (Just l)