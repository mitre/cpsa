(herald isoreject-corrected) 

(defprotocol isofix basic
  (defrole init (vars (a b name) (na nb nc text))
    (trace
     (send (cat a na))
     (recv (enc "first" nb na a (privk b)))
     (send (enc "second" nc nb b (privk a)))))
  (defrole resp (vars (a b name) (na nb nc text))
    (trace
     (recv (cat a na))
     (send (enc "first" nb na a (privk b)))
     (recv (enc "second" nc nb b (privk a))))
    (uniq-orig nb)))

(defskeleton isofix
  (vars (a b name))
  (defstrand resp 3 (a a) (b b))
  (non-orig (privk a) (privk b)))

(defskeleton isofix
  (vars (b name))
  (defstrand init 3 (b b))
  (non-orig (privk b)))
