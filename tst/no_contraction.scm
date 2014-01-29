(defprotocol no-contraction basic
  (defrole init
    (vars (a b name) (n text))
    (trace
     (send (enc (enc n (privk a))(pubk b)))))
  (defrole resp
    (vars (a name) (n text))
    (trace
     (recv (enc n (privk a))))))

(defskeleton no-contraction
  (vars (a b name) (n m text))
  (defstrand resp 1 (a a) (n n))
  (defstrand init 1 (n n))
  (uniq-orig n)
  (non-orig (privk a)))
