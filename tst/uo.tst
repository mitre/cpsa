(comment "CPSA 2.3.1")
(comment "All input read from uo.scm")

(defprotocol uniq-orig basic
  (defrole init (vars (n text)) (trace (send n)) (uniq-orig n))
  (defrole resp (vars (m n text)) (trace (send (enc m n)) (recv n))))

(defskeleton uniq-orig
  (vars (n m text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (m m) (n n))
  (uniq-orig n)
  (traces ((send n)) ((send (enc m n)) (recv n)))
  (label 0)
  (unrealized (1 1))
  (preskeleton)
  (comment "Not a skeleton"))

(defskeleton uniq-orig
  (vars (n m text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (m m) (n n))
  (precedes ((0 0) (1 1)))
  (uniq-orig n)
  (traces ((send n)) ((send (enc m n)) (recv n)))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0 1) ((n n) (m m))))
  (origs (n (0 0))))

(comment "Nothing left to do")
