(herald "Diffie-Hellman enhanced Needham-Schroeder-Lowe Protocol"
  (algebra diffie-hellman))

(defprotocol dhnsl diffie-hellman
  (defrole init
    (vars (a b name) (h2 h3 base) (x expn))
    (trace
     (send (enc (exp (gen) x) a (pubk b)))
     (recv (enc h2 (exp h2 x) h3 b (pubk a)))
     (send (enc (exp h3 x) (pubk b)))
    )
    (non-orig x)
    (comment "X should be assumed to be freshly chosen per role")
  )
  (defrole resp
    (vars (b a name) (h1 base) (y z expn))
    (trace
     (recv (enc h1 a (pubk b)))
     (send (enc (exp (gen) y) (exp h1 y) (exp (gen) z) b (pubk a)))
     (recv (enc (exp h1 z) (pubk b)))
    )
    (non-orig y z)
    (comment "Y and Z should be assumed to be freshly chosen per role")
  )
  (comment "Needham-Schroeder-Lowe DH challenge/responses in place of nonces")
)

;;; The initiator point-of-view
(defskeleton dhnsl
  (vars (a b name) (h2 h3 base) (x expn))
  (defstrand init 3 (a a) (b b) (h2 h2) (h3 h3) (x x))
  (non-orig (privk b) (privk a))
  (comment "Initiator point-of-view"))

;;; The responder point-of-view
(defskeleton ns
  (vars (a b name) (h1 base) (y z expn))
  (defstrand resp 3 (a a) (b b) (h1 h1) (y y) (z z))
  (non-orig (privk a))
  (comment "Responder point-of-view"))
