(herald "Print Test"
  (comment "See if read forms look like printed ones"))

(comment "CPSA 2.3.1")
(comment "All input read from print.scm")

(defprotocol print-test basic
  (defrole role
    (vars (a b akey) (f g skey) (x y data))
    (trace (recv (cat a b f g x y)))
    (comment "Check the order in which variables are printed")))

(defskeleton print-test
  (vars (x y data) (f g skey) (a b akey))
  (defstrand role 1 (x x) (y y) (f f) (g g) (a a) (b b))
  (comment "Check the order in which variables are printed")
  (traces ((recv (cat a b f g x y))))
  (label 0)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (f f) (g g) (x x) (y y))))
  (origs))

(comment "Nothing left to do")
