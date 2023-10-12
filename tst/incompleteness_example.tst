(herald incompleteness-example
  (comment "Shows a shape not found by CPSA"))

(comment "CPSA 4.4.3")
(comment "All input read from tst/incompleteness_example.scm")

(defprotocol incompleteness-example basic
  (defrole init
    (vars (k akey) (n text))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (k akey) (n1 n2 text))
    (trace (recv (enc n1 k)) (send n2)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton incompleteness-example
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (non-orig (invk k))
  (uniq-orig n)
  (traces ((send (enc n k)) (recv n)))
  (label 0)
  (unrealized (0 1))
  (dead)
  (origs (n (0 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol incompleteness-example basic
  (defrole init
    (vars (k akey) (n text))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (k akey) (n1 n2 text))
    (trace (recv (enc n1 k)) (send n2)))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton incompleteness-example
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (defstrand resp 2 (n1 n) (n2 n) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig n)
  (comment "A shape compatible with the first problem in this run")
  (traces ((send (enc n k)) (recv n)) ((recv (enc n k)) (send n)))
  (label 1)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")
