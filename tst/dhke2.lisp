(herald "Diffie-Hellman Key Exchange" (algebra diffie-hellman2))

;; The Diffie-Hellman problem is given (exp (gen) x), and (exp (gen)
;; y), compute the value of (exp (exp (gen) x) y) which is also (exp
;; (exp (gen) y) x).

(defprotocol dhke diffie-hellman2
  (defrole init (vars (a b name) (x expn) (h base))
    (trace
     (send (enc "i" (exp (gen) x) (privk a)))
     (recv (cat (enc h (privk b)) (enc a b (exp h x))))
     (send (enc "i" a b (exp h x))))
    (uniq-orig  (exp (gen) x)))
  (defrole resp (vars (a b name) (y expn) (h base))
    (trace
     (recv (enc "i" h (privk a)))
     (send (cat (enc (exp (gen) y) (privk b)) (enc a b (exp h y))))
     (recv (enc "i" a b (exp h y))))
    (uniq-orig (exp (gen) y))))

(defskeleton dhke (vars (a b name) (y expn) (h base))
  (defstrand resp 3 (a a) (b b) (y y) (h h))
  (non-orig (privk a) (privk b))
  (pen-non-orig (exp h y)))

 (defskeleton dhke (vars (a b name))
   (defstrand init 2 (a a) (b b))
   (non-orig (privk a) (privk b)))

(defprotocol dh-mim diffie-hellman2
  (defrole init
    (vars (x expn) (h base) (n text))
    (trace
     (send (exp (gen) x))
     (recv h)
     (send (enc n (exp h x))))
    (uniq-orig n (exp (gen) x)))
  (defrole resp
    (vars (y expn) (h base) (n text))
    (trace
     (recv h)
     (send (exp (gen) y))
     (recv (enc n (exp h y))))
    (uniq-orig (exp (gen) y)))
  (comment "Diffie-Hellman without signatures"
	   "has a man-in-the-middle attack"))

(defskeleton dh-mim
  (vars (n text))
  (defstrand init 3 (n n))
  (deflistener n)
  (uniq-orig n))

;; Protocols using variables of sort base

(comment
(defprotocol dhke-with-base-vars diffie-hellman
  (defrole init (vars (a b name) (g base) (x expn))
    (trace
     (send (enc "i" (exp (gen) x) (privk a)))
     (recv (cat (enc g (privk b)) (enc a b (exp g x))))
     (send (enc "i" a b (exp g x))))
    (uniq-orig  x))
  (defrole resp (vars (a b name) (h base) (y expn))
    (trace
     (recv (enc "i" h (privk a)))
     (send (cat (enc (exp (gen) y) (privk b)) (enc a b (exp h y))))
     (recv (enc "i" a b (exp h y))))
    (uniq-orig y)))

(defskeleton dhke-with-base-vars (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b)))

 (defskeleton dhke-with-base-vars (vars (a b name))
   (defstrand init 2 (a a) (b b))
   (non-orig (privk a) (privk b)))

(defprotocol dh-mim-with-base-vars diffie-hellman
  (defrole init
    (vars (x expn) (hy base) (n text))
    (trace
     (send (exp (gen) x))
     (recv hy)
     (send (enc n (exp hy x))))
    (uniq-orig n x))
  (defrole resp
    (vars (y expn) (hx base) (n text))
    (trace
     (recv hx)
     (send (exp (gen) y))
     (recv (enc n (exp hx y))))
    (uniq-orig y))
  (comment "Diffie-Hellman without signatures"
	   "has a man-in-the-middle attack"))

(defskeleton dh-mim-with-base-vars
  (vars (n text))
  (defstrand init 3 (n n))
  (defstrand resp 3 (n n))
  (uniq-orig n))

(defskeleton dh-mim-with-base-vars
  (vars (n text))
  (defstrand init 3 (n n))
  (deflistener n)
  (uniq-orig n))
)
