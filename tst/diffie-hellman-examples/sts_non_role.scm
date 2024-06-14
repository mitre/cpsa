;;; Station-to-station

;;; This is an authenticated form of a Diffie-Hellman key exchange.

;;; The file contains one model of the station-to-station protocol.
;;; An assumption is made that *any* initiator or responder properly
;;; picks a fresh random exponent and does not allow it to be obtained
;;; by the adversary.

(herald "Station-to-station protocol:  Weakened version"
	(bound 20)
	(algebra diffie-hellman))

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace
     (send (exp (gen) x))
     (recv (cat (exp (gen) eta)
		(enc (enc (exp (gen) eta)
			  (exp (gen) x) (privk b))
		     (exp (exp (gen) eta) x))))
     (send (enc (enc (exp (gen) x)
		     (exp (gen) eta) (privk a))
		(exp (exp (gen) eta) x)))
     (send (privk a)))
    ;; (uniq-gen x)
    )
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace
     (recv (exp (gen) chi))
     (send (cat (exp (gen) y)
		(enc (enc (exp (gen) y)
			  (exp (gen) chi) (privk b))
		     (exp (exp (gen) chi) y))))
     (recv (enc (enc (exp (gen) chi)
		     (exp (gen) y) (privk a))
		(exp (exp (gen) chi) y)))
     (send (privk b)))
    ;; (uniq-gen y)
    ))

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (uniq-gen x y)
  (non-orig (privk b) (privk a))
)

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (uniq-gen x y)
  (non-orig (privk a) (privk b))
  )

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (exp (exp (gen) y) x))
  (uniq-gen x y)
  (non-orig (privk b) (privk a)))

(defskeleton station-weak
  (vars (a b name) (x rndx) (eta expt))
  (defstrand init 3 (a a) (b b) (x x) (eta eta))
  (deflistener (exp (exp (gen) eta) x))
  (uniq-gen x)
  (non-orig (privk b) (privk a)))


(defskeleton station-weak
  (vars (a b name) (y rndx) (chi expt))
  (defstrand resp 3 (a a) (b b) (y y) (chi chi))
  (deflistener (exp (exp (gen) chi) y))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
)

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (eta y) (x x))
  (defstrand resp 4 (b b) (chi x) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-gen x y)
  (uniq-orig (privk b) (privk a))
  )

(defskeleton station-weak 
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (eta y) (x x))
  (defstrand resp 4 (b b) (chi x) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-gen x y)
  (uniq-orig (privk b) (privk a))
  )
