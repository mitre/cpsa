(herald "Diffie-Hellman Key Exchange" (algebra diffie-hellman))

;; The Diffie-Hellman problem is given (exp (gen) x), and (exp (gen)
;; y), compute the value of (exp (exp (gen) x) y) which is also (exp
;; (exp (gen) y) x).

(defprotocol dhke diffie-hellman
  (defrole init (vars (a b akey) (x y expn))
    (trace
     (send (enc "i" (exp (gen) x) (invk a)))
     (recv (cat (enc (exp (gen) y) (invk b))
		(enc a b (exp (exp (gen) y) x))))
     (send (enc "i" a b (exp (exp (gen) y) x))))
    (uniq-orig  x))
  (defrole resp (vars (a b akey) (x y expn))
    (trace
     (recv (enc "i" (exp (gen) x) (invk a)))
     (send (cat (enc (exp (gen) y) (invk b))
		(enc a b (exp (exp (gen) x) y))))
     (recv (enc "i" a b (exp (exp (gen) x) y))))
    (uniq-orig y)))

(defskeleton dhke (vars (a b akey))
  (defstrand resp 3 (a a) (b b))
  (non-orig (invk a) (invk b)))

 (defskeleton dhke (vars (a b akey))
   (defstrand init 2 (a a) (b b))
   (non-orig (invk a) (invk b)))
