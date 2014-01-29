(herald "Print Test"
  (comment "See if read forms look like printed ones"))

(defprotocol print-test basic
  (defrole role
    (vars (a b akey) (f g skey) (x y data))
    (trace (recv (cat a b f g x y)))
    (comment "Check the order in which variables are printed")))

(defskeleton print-test
  (vars (a b akey) (f g skey) (x y data))
  (defstrand role 1 (a a) (b b) (f f) (g g) (x x) (y y))
  (comment "Check the order in which variables are printed"))
