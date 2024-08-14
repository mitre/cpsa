module CPSA.DL.Simplifier (simplify) where

import CPSA.DL.Structs

simplify :: Query -> Query
simplify (Query name args f) =
    Query name args (simpForm f)

simpForm :: Formula -> Formula
simpForm f@(Atom _ _ _) =
    f
simpForm (Not _ (Not _ f)) =
    simpForm f
simpForm (Not vs f) =
    (Not vs (simpForm f))
simpForm (And _ [f]) =
    simpForm f
simpForm (And vs fs) =
    And vs (map simpForm fs)
simpForm (Or _ [f]) =
    simpForm f
simpForm (Or vs fs) =
    Or vs (map simpForm fs)
simpForm (Exists _ _ f) =
    simpForm f
simpForm (Diamond vs act f) =
    Diamond vs act (simpForm f)
