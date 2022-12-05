;;; Station-to-station

;;; This is an authenticated form of a Diffie-Hellman key exchange.

;;; The file contains a model of the station-to-station protocol.  An
;;; assumption is made that *any* initiator or responder properly
;;; picks a fresh random exponent and does not allow it to be obtained
;;; by the adversary.

;;; This version is weakened by not flipping the second signed msg.

(herald "Station-to-station protocol unflipped" (algebra diffie-hellman))

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace
     (send (exp (gen) x))
     (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
     (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
     (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace
     (recv h)
     (send (cat (exp (gen) y) (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
     (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
     (send (privk b)))
    (uniq-gen y))
)

(defskeleton station-to-station-unflip
  (vars (a b name))
  (defstrand init 3 (a a) (b b))
  (non-orig (privk b))
)

(defskeleton station-to-station-unflip
  (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a))
  )

(defskeleton station-to-station-unflip
  (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a))
  (facts (neq a b))
  )

(defskeleton station-to-station-unflip
  (vars (a b name)(x y rndx) (h base))
  (defstrand init 3 (a a) (b b) (x x) (h h))
  (deflistener (exp h x))
  (non-orig (privk b) (privk a))
)

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx)(h base))
  (defstrand resp 3 (a a) (b b) (y y) (h h))
  (deflistener (exp h y))
  (non-orig (privk a) (privk b))
)

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )
