{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module TseitinPredicates where

import SMTHelpers
import qualified Z3.Monad as Z3
import Syntax

import Control.Monad.State
import qualified Data.Data as Data
import qualified Data.List 
import qualified Data.Map as Map
import Data.Map ((!)) 
import qualified Data.Maybe as Maybe

import Data.Char (isAlphaNum)
import qualified Data.Set as Set

import Data.Graph
import Debug.Trace (trace)

-- domain = Fun "domain"

-- booleanDomain = Fun "booleanDomain"

-- funDomain = Fun "functionDomain"

-- type SBVec = SMT.BitVec
data PredNumConfig = Config
  { predNums :: Map.Map PredExpr Integer
  , configNumPreds :: Int
  , funVals :: Map.Map String VecFun
  , universalVars :: [BitVector]
  , existentialVars :: [String]
  , domain :: Z3.FuncDecl
  , booleanDomain :: Z3.FuncDecl
  , funDomain :: Z3.FuncDecl
  }

getNumPreds :: ConfigM Int
getNumPreds = gets configNumPreds

data ConfigM a = ConfigM (StateT PredNumConfig (Z3.Z3) a)
  deriving (Functor, Applicative, Monad, MonadIO, Z3.MonadZ3, MonadState PredNumConfig)


getAllFunctions :: ConfigM [VecFun]
getAllFunctions = gets (Map.elems . funVals)

--Generate a function that takes a bit-vector x
--and returns the SMT expression representing P_e(x)
--
pSMT :: (Z3.MonadZ3 z3) => PredNumConfig -> Expr -> BitVector -> z3 Z3.AST
pSMT config e x = 
  case e of
    (Var e) ->
      let i = (predNums config) Map.! (PVar e)
      in return $ ithBit i x (configNumPreds config)
    (FunApp e1 e2) -> 
      let i = (predNums config) Map.! (PFunApp e1 e2)
      in return $ ithBit i x (configNumPreds config)
    (Union e1 e2) -> (pSMT config e1 x) .\/ (pSMT config e2 x)
    (Intersect e1 e2) -> (pSMT config e1 x) ./\ (pSMT config e2 x)
    (Neg e) -> mNot (pSMT config e x)
    Top -> Z3.mkTrue
    Bottom -> Z3.mkFalse

p :: Expr -> BitVector -> ConfigM Z3.AST
p e x = do
  config <- get
  pSMT config e x 
-- p e x = do
--   n <- getNumPreds
--   i <- gets ((Map.! e) . predNums)
--     -- let xi = SMT.extract x (toInteger i) (toInteger i)
--   return $ ithBit i x n

ithBit i (BitVector x) n = x !!! (fromInteger i)

forallVar :: ConfigM BitVector
forallVar = head <$> forallVars 1

forallVars :: Int -> ConfigM [BitVector]
forallVars n = gets (take n . universalVars)

differentFuns :: VecFun -> ConfigM [(VecFun, Int)]
differentFuns f = do
  funMap <- gets funVals
  return [(g, arity g) | g <- Map.elems funMap, vecFunName g /= vecFunName f]

funNamed :: String -> ConfigM VecFun
funNamed f = do
  funs <- gets funVals
  return $ funs Map.! f

-- functionDomainClause :: Expr -> ConfigM Z3.AST
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
--       return $ eqCond /\ andAll neqConds
--     _ -> return $ SMT.bool True

booleanDomainClause :: BitVector -> Expr -> ConfigM Z3.AST
booleanDomainClause x e =
  case e of
    Var _ -> Z3.mkTrue
    Neg e2 -> 
      (p e x) .=== (mNot $ p e2 x)
    Union a b -> do
      (p e x) .=== (p a x .\/ p b x)
    Intersect a b -> do
      (p e x) .=== (p a x ./\ p b x)
    Top -> p e x
    Bottom -> do
      mNot $ p e x
    _ -> Z3.mkTrue

posConstrClause :: (Literal -> Z3.AST) -> BitVector -> Literal -> ConfigM Z3.AST
posConstrClause litVarFor x l@(Literal (e1, e2)) = 
  (return $ litVarFor l) .==> (p e1 x .==> p e2 x)

negConstrClause :: Integral i => (Literal -> Z3.AST) -> i -> Literal -> ConfigM Z3.AST
negConstrClause litVarFor numPreds l@(Literal (e1, e2)) = do
  x <- fresh numPreds
  pe1 <- p e1 x
  pe2 <- p e2 x
  --Assert that each existential variable is in our domain
  domainFun <- gets domain
  
  --And that it satisfies P_e1 and not P_e2 (i.e. e1 contains an element not in e2, i.e. e1 not subset of e2)
  (Z3.mkNot  $ litVarFor l) .==> ((domainFun $$ [x]) ./\ (p e1 x) ./\ (mNot $ p e2 x))

--Assert that the given function is closed over the domain
funClause :: VecFun -> ConfigM Z3.AST
funClause f = do
  n <- getNumPreds
  xs <- forallVars $ arity f
  fxs <-  f $$$ xs
  domainFun <- gets domain
  domainFun $$ [fxs]

initialState :: (Z3.MonadZ3 z3 ) => Int -> [BitVector] -> [PredExpr] -> [[PredExpr]] -> z3 PredNumConfig
initialState numBits vars exprs connComps = do
  let (predMap, numPreds) = allExprNums connComps
  let arities = Map.toList $ getArities  exprs
  funcDeclList <- forM arities $ \(f,ar) -> do
      bl <- Z3.mkBoolSort
      decls <- 
        forM [1 .. numBits] $ \bitnum -> 
            Z3.mkFreshFuncDecl (show f ++ "_" ++  "_ " ++ show bitnum ) (replicate (ar*numBits) bl) bl
      return _
  let funValList = [ (f, VecFun f ar decls)
              | (f, ar, decls) <- funcDeclList  
              ]
  return $ Config
        { predNums = predMap
        , configNumPreds = numPreds
        , funVals =
            Map.fromList funValList
        , universalVars = vars
        , existentialVars = []
        }

fresh :: Integral i => i -> ConfigM BitVector
fresh numPreds = do
  bl <- Z3.mkBoolSort 
  bits <- forM [1 .. numPreds] $ \_ -> Z3.mkFreshConst "x_exists" bl
  return $ BitVector bits
