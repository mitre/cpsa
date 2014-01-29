(defprotocol mass2 basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
      (send (cat a n2))
      (recv (cat n1 (enc n2 (ltk a b))))
      (send (enc n1 (ltk a b)))))
  (defrole resp
    (vars (a b name) (n1 n2 text))
    (trace
      (recv (cat a n2))
      (send (cat n1 (enc n2 (ltk a b))))
      (recv (enc n1 (ltk a b))))))

(defskeleton mass2
  (vars (a b name) (n1 text))
  (defstrand resp 3 (a a) (b b) (n1 n1))
  (non-orig (ltk a b))
  (uniq-orig n1))
