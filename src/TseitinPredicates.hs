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
module TseitinPredicates where

import SMTHelpers
import Data.SBV ( SBV, SBool, Symbolic, STuple, (.==), (.&&), (.||), (.=>), Predicate, sNot, sTrue, sFalse, uninterpret)
import qualified Data.SBV.Trans as SBV
import Syntax 

import Control.Monad.State
import qualified Data.Data as Data
import qualified Data.List 
import qualified Data.Map as Map
import Data.Map ((!))
import qualified Data.Maybe as Maybe

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

-- import Data.SBV.Tuple (untuple)


import Data.Graph
import Data.Constraint (Dict(..))


-- domain = Fun "domain"

-- booleanDomain = Fun "booleanDomain"

-- funDomain = Fun "functionDomain"

-- type SBVec = SMT.BitVec
-- type DictFor n = Dict (SymVal (Vec Bool n))
 
data PredNumConfig n = Config
  { predNums :: Map.Map PredExpr Int
  , configNumPreds :: SNat n
  , funVals :: Map.Map String (VecFun n)
  , universalVars :: [BitVector n]
  }

getNumPreds :: ConfigM n Int
getNumPreds = sNatToInt <$> gets configNumPreds

type ConfigM n = StateT (PredNumConfig n) (SBV.SymbolicT IO) 

getAllFunctions :: ConfigM n [VecFun n]
getAllFunctions = gets (Map.elems . funVals)

--Generate a function that takes a bit-vector x
--and returns the SMT expression representing P_e(x)
--
pSMT :: SNat n -> Map.Map PredExpr Int -> Expr -> BitVector n -> SBool
pSMT numPreds pnums e x = 
  case e of
    (Var e) ->
      let i = pnums Map.! (PVar e)
      in ithElem i x (numPreds)
    (FunApp e1 e2) -> 
      let i = pnums Map.! (PFunApp e1 e2)
      in ithElem i x (numPreds)
    (Union e1 e2) -> (pSMT numPreds pnums e1 x) .|| (pSMT numPreds pnums e2 x)
    (Intersect e1 e2) -> (pSMT numPreds pnums e1 x) .&& (pSMT numPreds pnums e2 x)
    (Neg e) -> sNot (pSMT numPreds pnums e x)
    Top -> sTrue
    Bottom -> sFalse

p :: Expr -> BitVector n -> ConfigM n SBool
p e x = do
  config <- get
  return $ pSMT (configNumPreds config) (predNums config) e x 
-- p e x = do
--   n <- getNumPreds
--   i <- gets ((Map.! e) . predNums)
--     -- let xi = SMT.extract x (toInteger i) (toInteger i)
--   return $ ithElem i x n




forallVar :: ConfigM n (BitVector n)
forallVar = head <$> forallVars 1

forallVars :: Int -> ConfigM n [BitVector n]
forallVars n = gets (take n . universalVars)

differentFuns :: VecFun n -> ConfigM n [(VecFun n, Int)]
differentFuns f = do
  funMap <- gets funVals
  return [(g, arity g) | g <- Map.elems funMap, vecFunName g /= vecFunName f]

funNamed :: String -> ConfigM n (VecFun n)
funNamed f = do
  funs <- gets funVals
  return $ funs Map.! f

-- functionDomainClause :: Expr -> ConfigM SMT.SExpr
-- functionDomainClause e = do
--   n <- getNumPreds
--   case e of
--     FunApp fname args -> do
--       f <- funNamed fname
--       xs <- forallVars (length args)
--       let fxs = bvApply n f xs
--       lhs <- p e fxs
--       rhs <- forM (zip args xs) $ \(ex, x) -> p ex x
--         --Need constraint that no g(...) is in f(...) set
--       let eqCond = andAll rhs === lhs
--       gs <- differentFuns f
--       neqConds <-
--         forM gs $ \(g, ar) -> do
--           xs <- forallVars ar
--           let gxs = bvApply n g xs
--           lhs <- p e gxs
--           return (lhs === SMT.bool False)
--       return $ eqCond .&& andAll neqConds
--     _ -> return $ SMT.bool True

-- booleanDomainClause :: BitVector n -> Expr -> ConfigM n SBool
-- booleanDomainClause x e =
--   case e of
--     Var _ -> return $ sTrue
--     Neg e2 -> do
--       pe <- p e x
--       pe2 <- p e2 x
--       return $ pe .== (sNot pe2)
--     Union a b -> do
--       pe <- p e x
--       pa <- p a x
--       pb <- p b x
--       return $ pe .== (pa .|| pb)
--     Intersect a b -> do
--       pe <- p e x
--       pa <- p a x
--       pb <- p b x
--       return $ pe .== (pa .&& pb)
--     Top -> p e x
--     Bottom -> do
--       px <- p e x
--       return $ sNot px
--     _ -> return $ sTrue

posConstrClause :: (Literal -> SBool) -> Literal -> ConfigM n (BitVector n -> SBool)
posConstrClause litVarFor l@(Literal (e1, e2)) = do
  pnums <- gets predNums
  numPreds <- gets configNumPreds  
  return $ \x -> (litVarFor l .=> ((pSMT numPreds pnums e1 x) .=> (pSMT numPreds pnums e2 x)))

negConstrClause :: (Literal -> SBool) -> SNat n -> (BitVector n -> SBool) -> Literal -> ConfigM n SBool
negConstrClause litVarFor numPreds domain l@(Literal (e1, e2)) = do
  x <- existsBitVec numPreds
  pe1 <- p e1 x
  pe2 <- p e2 x
  --Assert that each existential variable is in our domain
  let inDomain = domain x
  --And that it satisfies P_e1 and not P_e2 (i.e. e1 contains an element not in e2, i.e. e1 not subset of e2)
  return $ (sNot  $ litVarFor l) .=> (inDomain .&& pe1 .&& (sNot pe2))

--Assert that the given function is closed over the domain
funClause :: forall n .  (BitVector n -> SBool) -> VecFun n -> ConfigM n SBool
funClause domain f = do
  npreds <- gets configNumPreds
  xsList <- forallVars $ arity f
  case f of
    VecFun _ sn fun -> do
      case sn of
        (_ :: SNat nar) -> do
            let xs = makeSVec sn xsList
            let fxs = fun xs
            return $ domain fxs

-- freshVecFun :: forall n . SNat n -> String -> Int -> VecFun n
-- freshVecFun numBits name ar = 
--   case toENat ar of
--     (ENat sn_arity ) -> case sn_arity of
--       (_ :: SNat nar) -> VecFun @nar @n name sn_arity $ case vecInstance @Bool @n numBits of
--         Dict -> case vecInstance @(Vec Bool n) @nar sn_arity of
--           Dict -> uninterpret name

-- initialState :: forall n . SNat n -> [BitVector n] -> [PredExpr] -> [[PredExpr]] -> PredNumConfig n
-- initialState numBits vars exprs connComps =
--   let (predMap, _) = allExprNums connComps
--    in Config
--         { predNums = predMap
--         , configNumPreds = numBits
--         , funVals =
--             Map.fromList
--               [ (f, freshVecFun numBits f ar )
--               | (f, ar) <- Map.toList $ getArities  exprs 
--               ]
--         , universalVars = vars
--         , bitVecInst = vecInstance @Bool @n numBits
--         , domainFun = case vecInstance @Bool @n numBits of
--           Dict -> uninterpret "inDomain"
--         }


