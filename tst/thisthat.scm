(herald "Needham-Schroeder Public-Key Protocol This-That Variant")

(defprotocol thisthat basic
  (defrole init
    (vars (a b name) (n1 n2 n3 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (cat (enc n1 n2 (pubk a)) (enc n1 n3 (pubk a))))
     (recv (cat (enc "this" n2 (pubk b)) (enc "that" n3 (pubk b))))))
  (defrole this
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 (pubk a)))
     (send (enc "this" n2 (pubk b))))
    (uniq-orig n2))
  (defrole that
    (vars (b a name) (n3 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n3 (pubk a)))
     (send (enc "that" n3 (pubk b))))
    (uniq-orig n3)))

;;; The initiator point-of-view
(defskeleton thisthat
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (comment "Initiator point-of-view"))
