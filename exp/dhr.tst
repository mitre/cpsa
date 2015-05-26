(herald dhr (algebra diffie-hellman))

(comment "CPSA 2.5.0")
(comment "All input read from dhr.scm")

(defprotocol dhr diffie-hellman
  (defrole init (vars (x y expn)) (trace (send (exp (gen) (mul x y)))))
  (comment "Shows a failure with generalization"
    "Run this with a step count of 4"))

(defskeleton dhr
  (vars (x y expn))
  (defstrand init 1 (x y) (y x))
  (traces ((send (exp (gen) (mul x y)))))
  (label 0)
  (unrealized)
  (shape)
  (maps ((0) ((x y) (y x))) ((0) ((x x) (y y))))
  (origs))

(comment "Nothing left to do")
