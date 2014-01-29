(defprotocol dh_mim reduced-diffie-hellman
  (defrole init
    (vars (x expn) (hy base) (n text))
    (trace (send (gen x)) (recv hy) (send (enc n (exp hy x))))
    (uniq-orig n x))
  (defrole resp
    (vars (y expn) (hx base) (n text))
    (trace (recv hx) (send (gen y)) (recv (enc n (exp hx y))))
    (uniq-orig y))
  (comment "Diffie-hellman key exchange followed by an encryption"))

(defskeleton dh_mim
  (vars (n text) (hx hy base) (x y expn))
  (defstrand init 3 (n n) (hy hy) (x x))
  (defstrand resp 3 (n n) (hx hx) (y y))
  (precedes ((0 2) (1 2)))
  (uniq-orig n x y)
  (comment "Agreement on the encrypted text only"))

(defprotocol dh_mim reduced-diffie-hellman-with-penetrator
  (defrole init
    (vars (x expn) (hy base) (n text))
    (trace (send (gen x)) (recv hy) (send (enc n (exp hy x))))
    (uniq-orig n x))
  (defrole resp
    (vars (y expn) (hx base) (n text))
    (trace (recv hx) (send (gen y)) (recv (enc n (exp hx y))))
    (uniq-orig y))
  (defrole pen-exp
    (vars (x expn) (h base))
    (trace (recv x) (recv h) (send (exp h x))))
  (defrole pen-make
    (vars (x expn))
    (trace (send x)))
  (defrole pen-gen
    (vars (x expn))
    (trace (recv x) (send (gen x))))
  (defrole pen-dec
    (vars (x mesg) (h base))
    (trace (recv (enc x h)) (recv h) (send x)))
  (defrole pen-enc
    (vars (x mesg) (h base))
    (trace (recv x) (recv h) (send (enc x h)))))

(defskeleton dh_mim
  (vars (n text) (hx hy base) (x y expn))
  (defstrand init 3 (n n) (hy (gen v)) (x x))
  (defstrand resp 3 (n n) (hx (gen u)) (y y))
  (defstrand pen-make 1 (x u))
  (defstrand pen-make 1 (x v))
  (defstrand pen-gen 2 (x u))
  (defstrand pen-gen 2 (x v))
  (defstrand pen-exp 3 (x v) (h (gen x)))
  (defstrand pen-dec 3 (x n) (h (exp (gen x) v)))
  (defstrand pen-exp 3 (x u) (h (gen y)))
  (defstrand pen-enc 3 (x n) (h (exp (gen y) u)))
  (precedes ((2 0) (4 0)) ((3 0) (5 0))
	    ((4 1) (1 0)) ((5 1) (0 1))
	    ((0 0) (6 1)) ((3 0) (6 0))
	    ((0 2) (7 0)) ((6 2) (7 1))
	    ((7 2) (9 0)) ((9 2) (1 2))
	    ((1 1) (8 1)) ((9 1) (8 2))
	    ((2 0) (8 0)))
  (uniq-orig n x y)
  (comment "Bundle"))
