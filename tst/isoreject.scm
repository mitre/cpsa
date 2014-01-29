(defprotocol isoreject basic
  (defrole init (vars (a b name) (na nb nc text))
    (trace
     (send (cat a na))
     (recv (enc nb na a (privk b)))
     (send (enc nc nb b (privk a)))))
  (defrole resp (vars (a b name) (na nb nc text))
    (trace
     (recv (cat a na))
     (send (enc nb na a (privk b)))
     (recv (enc nc nb b (privk a))))
    (uniq-orig nb)))

(defskeleton isoreject
  (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b)))

(defskeleton isoreject
  (vars (b name))
  (defstrand init 3 (b b))
  (non-orig (privk b)))
