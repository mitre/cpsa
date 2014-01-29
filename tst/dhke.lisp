(herald "Diffie-Hellman Key Exchange" (algebra diffie-hellman))

;; The Diffie-Hellman problem is given (exp (gen) x), and (exp (gen)
;; y), compute the value of (exp (exp (gen) x) y) which is also (exp
;; (exp (gen) y) x).

(defprotocol dhke diffie-hellman
  (defrole init (vars (a b name) (x y expn))
    (trace
     (send (enc "i" (exp (gen) x) (privk a)))
     (recv (cat (enc (exp (gen) y) (privk b)) (enc a b (exp (exp (gen) y) x))))
     (send (enc "i" a b (exp (exp (gen) y) x))))
    (uniq-orig  x))
  (defrole resp (vars (a b name) (x y expn))
    (trace
     (recv (enc "i" (exp (gen) x) (privk a)))
     (send (cat (enc (exp (gen) y) (privk b)) (enc a b (exp (exp (gen) x) y))))
     (recv (enc "i" a b (exp (exp (gen) x) y))))
    (uniq-orig y)))

(defskeleton dhke (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b)))

 (defskeleton dhke (vars (a b name))
   (defstrand init 2 (a a) (b b))
   (non-orig (privk a) (privk b)))

(defprotocol dh-mim diffie-hellman
  (defrole init
    (vars (x y expn) (n text))
    (trace
     (send (exp (gen) x))
     (recv (exp (gen) y))
     (send (enc n (exp (exp (gen) y) x))))
    (uniq-orig n x))
  (defrole resp
    (vars (x y expn) (n text))
    (trace
     (recv (exp (gen) x))
     (send (exp (gen) y))
     (recv (enc n (exp (exp (gen) x) y))))
    (uniq-orig y))
  (comment "Diffie-Hellman without signatures"
	   "has a man-in-the-middle attack"))

(defskeleton dh-mim
  (vars (n text))
  (defstrand init 3 (n n))
  (deflistener n)
  (uniq-orig n))

;; Protocols using variables of sort base

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
