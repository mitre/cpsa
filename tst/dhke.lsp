(herald "Diffie-Hellman Key Exchange" (algebra diffie-hellman))

;; The Diffie-Hellman problem is given (exp (gen) x), and (exp (gen)
;; y), compute the value of (exp (exp (gen) x) y) which is also (exp
;; (exp (gen) y) x).

(defprotocol dhke diffie-hellman
  (defrole init (vars (a b name) (h base) (x expn))
    (trace
     (send (enc "i" (exp (gen) x) (privk a)))
     (recv (cat (enc h (privk b)) (enc a b (exp h x))))
     (send (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (defrole resp (vars (a b name) (h base) (x expn))
    (trace
     (recv (enc "i" h (privk a)))
     (send (cat (enc (exp (gen) x) (privk b)) (enc a b (exp h x))))
     (recv (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x))))

(defskeleton dhke (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b)))

(defskeleton dhke (vars (a b name))
  (defstrand init 2 (a a) (b b))
  (non-orig (privk a) (privk b)))

(defprotocol dh-mim diffie-hellman
  (defrole init
    (vars (h base) (x expn) (n text))
    (trace
     (send (exp (gen) x))
     (recv h)
     (send (enc n (exp h x))))
    (non-orig x)
    (uniq-orig n (exp (gen) x)))
  (defrole resp
    (vars (h base) (x expn) (n text))
    (trace
     (recv h)
     (send (exp (gen) x))
     (recv (enc n (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (comment "Diffie-Hellman without signatures"
	   "has a man-in-the-middle attack"))

(defskeleton dh-mim
  (vars (n text))
  (defstrand init 3 (n n))
  (deflistener n)
  (uniq-orig n))
