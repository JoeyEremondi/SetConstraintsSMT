module TseitinPredicates where

import SMTHelpers
import qualified SimpleSMT as SMT hiding (bvBin, tBits)
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

domain = Fun "domain"

booleanDomain = Fun "booleanDomain"

funDomain = Fun "functionDomain"

-- type SBVec = SMT.BitVec
data PredNumConfig = Config
  { varNums :: Map.Map PVar Integer
  , appNums :: Map.Map PFunApp Integer
  , configNumPreds :: Int
  , funVals :: Map.Map String VecFun
  , universalVars :: [BitVector]
  , existentialVars :: [String]
  }

getNumPreds :: ConfigM Int
getNumPreds = gets configNumPreds

type ConfigM = State PredNumConfig

getAllFunctions :: ConfigM [VecFun]
getAllFunctions = gets (Map.elems . funVals)

--Generate a function that takes a bit-vector x
--and returns the SMT expression representing P_e(x)
--
pSMT :: PredNumConfig -> Expr -> BitVector -> SMT.SExpr
pSMT config e x = 
  case e of
    (Var e) ->
      let i = (varNums config) Map.! (PVar e)
      in ithBit i x (configNumPreds config)
    (FunApp e1 e2) -> 
      let i = (appNums config) Map.! (PFunApp (e1, e2))
      in ithBit i x (configNumPreds config)
    (Union e1 e2) -> (pSMT config e1 x) \/ (pSMT config e2 x)
    (Intersect e1 e2) -> (pSMT config e1 x) /\ (pSMT config e2 x)
    (Neg e) -> SMT.not (pSMT config e x)
    Top -> SMT.bool True
    Bottom -> SMT.bool False

p :: Expr -> BitVector -> ConfigM SMT.SExpr
p e x = do
  config <- get
  return $ pSMT config e x 
-- p e x = do
--   n <- getNumPreds
--   i <- gets ((Map.! e) . predNums)
--     -- let xi = SMT.extract x (toInteger i) (toInteger i)
--   return $ ithBit i x n

ithBit i (BitVector x) n = SMT.eq (SMT.Atom "#b1") (SMT.extract x i i)

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
--       return $ eqCond /\ andAll neqConds
--     _ -> return $ SMT.bool True

booleanDomainClause :: BitVector -> Expr -> ConfigM SMT.SExpr
booleanDomainClause x e =
  case e of
    Var _ -> return $ SMT.bool True
    Neg e2 -> do
      pe <- p e x
      pe2 <- p e2 x
      return $ pe === (SMT.not pe2)
    Union a b -> do
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe === (pa \/ pb)
    Intersect a b -> do
      pe <- p e x
      pa <- p a x
      pb <- p b x
      return $ pe === (pa /\ pb)
    Top -> p e x
    Bottom -> do
      px <- p e x
      return $ SMT.not px
    _ -> return $ SMT.bool True

posConstrClause :: (Literal -> SMT.SExpr) -> BitVector -> Literal -> ConfigM SMT.SExpr
posConstrClause litVarFor x l@(Literal (e1, e2)) = do
  pe1 <- p e1 x
  pe2 <- p e2 x
  return $ (litVarFor l ==> (pe1 ==> pe2))

negConstrClause :: Integral i => (Literal -> SMT.SExpr) -> i -> Literal -> ConfigM SMT.SExpr
negConstrClause litVarFor numPreds l@(Literal (e1, e2)) = do
  x <- fresh numPreds
  pe1 <- p e1 x
  pe2 <- p e2 x
  --Assert that each existential variable is in our domain
  let inDomain = domain $$$ [x]
  --And that it satisfies P_e1 and not P_e2 (i.e. e1 contains an element not in e2, i.e. e1 not subset of e2)
  return $ (SMT.not  $ litVarFor l) ==> (inDomain /\ pe1 /\ (SMT.not pe2))

--Assert that the given function is closed over the domain
funClause :: VecFun -> ConfigM SMT.SExpr
funClause f = do
  n <- getNumPreds
  xs <- forallVars $ arity f
  let fxs = bvApply n f xs
  return $ domain $$$ [fxs]

initialState :: Int -> [BitVector] -> PredExprs -> PredNumConfig
initialState numBits vars exprs  =
  let (varMap, funAppMap, numPreds) = allExprNums exprs
   in Config
        { varNums = varMap
        , appNums = funAppMap
        , configNumPreds = numPreds
        , funVals = 
            Map.fromList
              [ (f, VecFun f (replicate ar [0 .. numBits - 1]))
              | (f, ar) <- Map.toList $ getArities (pfunApps exprs) 
              ]
        , universalVars = vars
        , existentialVars = []
        }

fresh :: Integral i => i -> ConfigM BitVector
fresh numPreds = do
  state <- get
  n <- getNumPreds
  let oldVars = existentialVars state
      takenVars = Set.fromList oldVars
      varNames = map (\i -> "x_exists_" ++ show i) [0 ..]
      validVars = filter (\x -> not $ x `Set.member` takenVars) varNames
      newVar = head validVars
      newState = state {existentialVars = newVar : oldVars}
  put newState
  return $ BitVector $ SMT.Atom newVar 
 