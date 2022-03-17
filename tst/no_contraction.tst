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
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

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
