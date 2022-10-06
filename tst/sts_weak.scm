;;; Station-to-station weak

;;; This is an authenticated form of a Diffie-Hellman key exchange.

;;; The file contains one model of the station-to-station protocol.
;;; It weakens the previous model by omitting an assumption.  

;;; Namely, we do not assume that *every* initiator or responder
;;; properly picks a fresh random exponent and does not allow it to be
;;; obtained by the adversary.

(herald "Station-to-station protocol:  Weakened version" (algebra diffie-hellman))


(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x expn) (h base) (a b name))
    (trace
     (send (exp (gen) x))
     (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
     (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
     (send (privk a)))
  )
  (defrole resp
    (vars (y expn) (h base) (a b name))
    (trace
     (recv h)
     (send (cat (exp (gen) y) (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
     (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
     (send (privk b)))
    (absent (y h))
    )
)

(defskeleton station-weak
  (vars (a b name) (x expn))
  (defstrand init 3 (a a) (b b) (x x))
  (uniq-gen x)
  (non-orig (privk b) (privk a))
)

(defskeleton station-weak
  (vars (a b name) (y expn))
  (defstrand resp 3 (a a) (b b) (y y))
  (uniq-gen y)
  (non-orig (privk a) (privk b))
)

(defskeleton station-weak
  (vars (a b name)(x y expn) (h base))
  (defstrand init 3 (a a) (b b) (x x) (h h))
  (deflistener (exp h x))
  (non-orig (privk b) (privk a))
)

(defskeleton station-weak
  (vars (a b name) (x y expn)(h base))
  (defstrand resp 3 (a a) (b b) (y y) (h h))
  (deflistener (exp h y))
  (non-orig (privk a) (privk b))
)


(defskeleton station-weak
  (vars (a b name) (x y expn))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )

(defskeleton station-weak
  (vars (a b name) (x y expn))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk b) (privk a))
  )
