;;; Station-to-station

;;; This is an authenticated form of a Diffie-Hellman key exchange.

;;; The file contains one model of the station-to-station protocol.
;;; We weaken it here by omitting the flip in the order of components
;;; in the second and third msgs.

(herald "station-to-station-reflect protocol" (bound 20) (algebra diffie-hellman))

(defprotocol station-to-station-reflect diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace
     (send (exp (gen) x))
     (recv (cat (exp (gen) eta)
		(enc (enc (exp (gen) eta)
			  (exp (gen) x) (privk b))
		     (exp (exp (gen) eta) x))))
     (send (enc (enc (exp (gen) eta)
		     (exp (gen) x) (privk a))
		(exp (exp (gen) eta) x)))
     (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace
     (recv (exp (gen) chi))
     (send (cat (exp (gen) y)
		(enc (enc (exp (gen) y)
			  (exp (gen) chi) (privk b))
		     (exp (exp (gen) chi) y))))
     (recv (enc (enc (exp (gen) y)
		     (exp (gen) chi) (privk a))
		(exp (exp (gen) chi) y)))
     (send (privk b)))
    (uniq-gen y)))

(defskeleton station-to-station-reflect
  (vars (a b name))
  (defstrand init 3 (a a) (b b))
  (non-orig (privk b) (privk a))
)

(defskeleton station-to-station-reflect
  (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b))
  )

(defskeleton station-to-station-reflect
  (vars (a b name)(x y rndx) (eta expt))
  (defstrand init 3 (a a) (b b) (x x) (eta eta))
  (deflistener (exp (exp (gen) eta) x))
  (non-orig (privk b) (privk a))
)

(defskeleton station-to-station-reflect
  (vars (a b name) (x y rndx)(chi expt))
  (defstrand resp 3 (a a) (b b) (y y) (chi chi))
  (deflistener (exp (exp (gen) chi) y))
  (non-orig (privk a) (privk b))
)

(defskeleton station-to-station-reflect
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (eta y) (x x))
  (defstrand resp 4 (b b) (chi x) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )

(defskeleton station-to-station-reflect
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (eta y) (x x))
  (defstrand resp 4 (b b) (chi x) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )
