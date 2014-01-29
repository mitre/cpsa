(herald incompleteness-example
  (comment "Shows a shape not found by CPSA"))

(defprotocol incompleteness-example basic
  (defrole init (vars (k akey) (n text))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp (vars (k akey) (n1 n2 text))
    (trace (recv (enc n1 k)) (send n2))))

(defskeleton incompleteness-example
  (vars (k akey))
  (defstrand init 2 (k k))
  (non-orig (invk k)))

(defskeleton incompleteness-example
  (vars (k akey) (n text))
  (defstrand init 2 (k k) (n n))
  (defstrand resp 2 (k k) (n1 n) (n2 n))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (comment "A shape compatible with the first problem in this run"))
