module SetConstraints.Solve 
    (   Syntax.Expr(..), Syntax.CExpr(..), ArgParse.Options(..), Syntax.withProjection, Syntax.withProjectionLhs,
        Syntax.Projection(..), solve) where

import qualified SolveSetConstraints as InternalSolve
import qualified Syntax
import qualified ArgParse

solve :: ArgParse.Options -> (Syntax.CExpr) -> IO (Either String () )
solve options constr = do
    InternalSolve.solveSetConstraints options constr 