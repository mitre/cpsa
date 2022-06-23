(comment "CPSA 4.3.1")
(comment "All input read from tst/no_contraction.scm")

(defprotocol no-contraction basic
  (defrole init
    (vars (a b name) (n text))
    (trace (send (enc (enc n (privk a)) (pubk b)))))
  (defrole resp
    (vars (a name) (n text))
    (trace (recv (enc n (privk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton no-contraction
  (vars (n text) (a a-0 b name))
  (defstrand resp 1 (n n) (a a))
  (defstrand init 1 (n n) (a a-0) (b b))
  (non-orig (privk a))
  (uniq-orig n)
  (traces ((recv (enc n (privk a))))
    ((send (enc (enc n (privk a-0)) (pubk b)))))
  (label 0)
  (unrealized (0 0))
  (preskeleton)
  (origs (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton no-contraction
  (vars (n text) (a a-0 b name))
  (defstrand resp 1 (n n) (a a))
  (defstrand init 1 (n n) (a a-0) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk a))
  (uniq-orig n)
  (traces ((recv (enc n (privk a))))
    ((send (enc (enc n (privk a-0)) (pubk b)))))
  (label 1)
  (parent 0)
  (unrealized (0 0))
  (origs (n (1 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton no-contraction
  (vars (n text) (a b name))
  (defstrand resp 1 (n n) (a a))
  (defstrand init 1 (n n) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation encryption-test (displaced 2 1 init 1) (enc n (privk a-0))
    (0 0))
  (traces ((recv (enc n (privk a))))
    ((send (enc (enc n (privk a)) (pubk b)))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (n n) (a-0 a) (b b))))
  (origs (n (1 0))))

(comment "Nothing left to do")
