module SetConstraints.Solve 
    (   Syntax.Expr(..), Syntax.CExpr(..), ArgParse.Options(..), Syntax.withProjection, Syntax.withProjectionLhs,
        Syntax.Projection(..), solve) where

import qualified SolveSetConstraints as InternalSolve
import qualified Syntax
import qualified ArgParse
import SMTHelpers (makeSolver)

solve :: ArgParse.Options -> (Syntax.CExpr) -> IO (Either String () )
solve options constr = do
    s <- makeSolver options
    InternalSolve.solveSetConstraints s options (Syntax.Top, constr)