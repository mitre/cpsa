(herald dhr (algebra diffie-hellman))

(defprotocol dhr diffie-hellman
  (defrole init (vars (x y expn))
    (trace (send (exp (gen) (mul x y)))))
  (comment "Shows a failure with generalization"
	   "Run this with a step count of 4"))

(defskeleton dhr
  (vars)
  (defstrand init 1))
