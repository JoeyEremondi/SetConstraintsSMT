module SMTHelpers where

import qualified SimpleSMT as SMT

($$) :: String -> [SMT.SExpr] -> SMT.SExpr
f $$ [] = (SMT.Atom f)
f $$ args = SMT.List (SMT.Atom f : args)

($$$) :: (Monad m) => String -> [SMT.SExpr] -> m SMT.SExpr
f $$$ [] = return (SMT.Atom f)
f $$$ args = return $ SMT.List (SMT.Atom f : args)

iff a b = (a ==> b) /\ (b ==> a)

(===) = SMT.eq

(/\) = SMT.and

(\/) = SMT.or

(==>) = SMT.implies

(<==>) = iff

--tString = SMT.Atom "String"
--tList t = "List" $$ [t]
andAll l =
  case l of
    [] -> SMT.bool True
    _ -> "and" $$ l

-- string s = SMT.Atom $ ['"'] ++ s ++ ['"']
-- slCons h t = "insert" $$ [t, h]
-- sList = foldl slCons (SMT.Atom "nil")
-- applyList f n l = f $$ (map (nthElem l) [0 .. n - 1])
-- nthElem :: SMT.SExpr -> Int -> SMT.SExpr
-- nthElem l 0 = "head" $$ [l]
-- nthElem l n = nthElem ("tail" $$ [l]) (n - 1)
sshow s = SMT.showsSExpr s ""

vshow = sshow . SMT.value
