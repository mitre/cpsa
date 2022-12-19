(comment "CPSA 4.4.1")
(comment "All input read from tst/uo.scm")

(defprotocol uniq-orig basic
  (defrole init (vars (n text)) (trace (send n)) (uniq-orig n))
  (defrole resp (vars (m n text)) (trace (send (enc m n)) (recv n)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniq-orig
  (vars (n m text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (m m) (n n))
  (uniq-orig n)
  (traces ((send n)) ((send (enc m n)) (recv n)))
  (label 0)
  (unrealized (1 1))
  (preskeleton)
  (origs (n (0 0)))
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
  (realized)
  (shape)
  (maps ((0 1) ((n n) (m m))))
  (origs (n (0 0))))

(comment "Nothing left to do")
