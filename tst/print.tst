(herald "Print Test"
  (comment "See if read forms look like printed ones"))

(comment "CPSA 4.4.1")
(comment "All input read from tst/print.scm")

(defprotocol print-test basic
  (defrole role
    (vars (a b akey) (f g skey) (x y data))
    (trace (recv (cat a b f g x y)))
    (comment "Check the order in which variables are printed"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton print-test
  (vars (x y data) (f g skey) (a b akey))
  (defstrand role 1 (x x) (y y) (f f) (g g) (a a) (b b))
  (comment "Check the order in which variables are printed")
  (traces ((recv (cat a b f g x y))))
  (label 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (f f) (g g) (x x) (y y))))
  (origs))

(comment "Nothing left to do")
