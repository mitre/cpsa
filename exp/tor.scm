(herald "Tor Circuit-Level Handshake Protocol" (algebra diffie-hellman)
  (comment "Achieves unilateral authentication"))

;; Hashing--no one can extract a key from an encryption

(defmacro (hash x)
  (enc "hash" x))

(defprotocol tor diffie-hellman
  (defrole init
    (vars (x y expn) (b name) (n text) (kh akey))
    (trace
     (send (enc (exp (gen) x) (pubk b)))
     (recv (cat (exp (gen) y) (hash (cat (exp (exp (gen) x) y)))))
     (send (enc n (exp (exp (gen) y) x))))
    (pen-non-orig x)
    (uniq-orig n))
  (defrole resp
    (vars (x y expn) (b name) (n text) (kh akey))
    (trace
     (recv (enc (exp (gen) x) (pubk b)))
     (send (cat (exp (gen) y) (hash (cat (exp (exp (gen) x) y)))))
     (recv (enc n (exp (exp (gen) x) y))))
    (pen-non-orig y)))

(defskeleton tor
  (vars (b name) (n text))
  (defstrand init 2 (b b))
  (non-orig (privk b)))

(defskeleton tor
  (vars (b name) (n text))
  (defstrand resp 3 (b b))
  (non-orig (privk b)))

(defskeleton tor
  (vars (b name) (n text))
  (defstrand init 3 (b b) (n n))
  (deflistener n)
  (non-orig (privk b)))
