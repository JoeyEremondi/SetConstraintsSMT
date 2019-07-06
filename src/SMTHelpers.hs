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

import Control.Monad
import Data.Char (digitToInt)
import qualified Data.List as List
import qualified Data.SBV as SMT
import Data.SBV (SymVal, SBV, SBool, Symbolic, STuple, (.==), (.&&), (.||), (.=>))
import ArgParse

import Data.Data (Data)

import Data.SBV.Tuple (tuple)

import Data.Constraint (Dict(..))


-- data VecFun = VecFun
--   { vecFunName :: String
--   , argUsedBits :: [[Int]]
--   } deriving (Eq, Ord, Read)

-- instance Show VecFun where
--   show = vecFunName

-- arity :: VecFun -> Int
-- arity = length . argUsedBits

-- defineFun s (Fun f) = SMT.defineFun s f

-- declareFun s (FuadeclareFun s f

-- getBitVec :: SMTaBitVector -> IO BitVector
-- getBitVec s bv =a
--   forM bv $ \bit -> do
--     v <- SMT.getExpr s bit
--     return $ SMT.value v

data Nat = 
  Z | S Nat

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

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
eSucc (ENat s) = ENat (SS s)

toENat :: Int -> ENat
toENat 1 = ENat (SZ)
toENat sn = eSucc (toENat n)
  where n = sn - 1
        -- (ENat (en :: SNat n))  = toENat n
         

newtype Fun = Fun
  { unFun :: String
  } deriving (Eq, Ord, Show, Read)


type family Vec a (n :: Nat) where
  Vec a Z = a
  Vec a (S n) = (a, Vec a n)
  -- deriving (Read, Data, Show, SMT.HasKind, SymVal)

  -- deriving (Read, Data, Show, SMT.HasKind, SymVal)


type SVec a n = SBV (Vec a n)


vecInstance :: forall a (n :: Nat) . (SymVal a) => SNat n -> Dict (SymVal (Vec a n))
vecInstance sz@SZ = 
  case sz of
    (_ :: SNat Z) -> Dict
vecInstance ss@(SS n) = 
  case ss of
    (_ :: SNat (S n')) -> 
      case vecInstance @a @n' n of
        Dict -> Dict 

makeSVec :: forall a (n :: Nat) . (SymVal a) => SNat n -> [SBV a] -> SVec a n
makeSVec sz@SZ [elem] = 
  case sz of
    (_ :: SNat Z) -> elem
makeSVec ss@(SS npred) (first:rest) = 
  case ss of
    (_ :: SNat (S n')) -> 
      case (makeSVec @a @n' npred rest, vecInstance @a @n' npred) of
        (vecRest, Dict) -> tuple (first, vecRest) 

type BitVector n = SVec Bool n 
type FunArgs arity n = SVec (Vec Bool n) arity
type Constructor arity n = FunArgs arity n -> BitVector n
type InDomain n = (BitVector n) -> SBool

data VecFun :: Nat -> * where
  VecFun :: forall arity n . String -> SNat arity -> Constructor arity n -> VecFun n

arity (VecFun _ sn _) = sNatToInt sn
vecFunName (VecFun name _ _) = name

-- makeBitVector :: [SBool] -> EBitVector 
-- makeBitVector [e] = EBitVector $ (BitVector e :: BitVector Z)
-- makeBitVector (first : rest) = EBitVector $ BitVector (first, bvRest)
--   where (EBitVector bvRest) = makeBitVector rest

-- instance Show BitVector where
--   show (BitVector s) = show $ toDec $ map toBit s
--       -- https://stackoverflow.com/questions/5921573/convert-a-string-representing-a-binary-number-to-a-base-10-string-haskell
--     where
--       toBit (SMT.Atom "true") = '1'
--       toBit (SMT.Atom "false") = '0'
--       toDec :: String -> Int
--       toDec = List.foldl' (\acc x -> acc * 2 + digitToInt x) 0






-- declareVec :: SMT.Solver -> [Char] -> [SMT.SExpr] -> IO [SMT.SExpr]
-- declareVec s fullName types =
--   forM (zip (nameToBitNames (length types) fullName) types) $ \(nm, t) ->
--     SMT.declare s nm t

-- declareFunVec ::
--      SMT.Solver -> [Char] -> [SMT.SExpr] -> [SMT.SExpr] -> IO [SMT.SExpr]
-- declareFunVec s fullName argTypes retTypes =
--   forM (zip (nameToBitNames (length retTypes) fullName) retTypes) $ \(nm, rtype) ->
--     SMT.declareFun s nm argTypes rtype

-- defineFunVec = error "TODO"

-- forAll :: [(SMT.SExpr, SMT.SExpr)] -> SMT.SExpr -> SMT.SExpr
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