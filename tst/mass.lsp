(defprotocol mass basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
      (send a)
      (recv n1)
      (send (enc n1 (ltk a b)))
      (send n2)
      (recv (enc n2 (ltk a b)))))
  (defrole resp
    (vars (a b name) (n1 n2 text))
    (trace
      (recv a)
      (send n1)
      (recv (enc n1 (ltk a b)))
      (recv n2)
      (send (enc n2 (ltk a b))))))

(defskeleton mass
  (vars (a b name) (n2 text))
  (defstrand init 5 (a a) (b b) (n2 n2))
  (non-orig (ltk a b))
  (uniq-orig n2))

(defskeleton mass
  (vars (a b name) (n1 text))
  (defstrand resp 5 (a a) (b b) (n1 n1))
  (non-orig (ltk a b))
  (uniq-orig n1))
