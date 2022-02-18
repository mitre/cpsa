(comment "CPSA 4.3.0")
(comment "All input read from tst/isoreject.scm")

(defprotocol isoreject basic
  (defrole init
    (vars (a b name) (na nb nc text))
    (trace (send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a)))))
  (defrole resp
    (vars (a b name) (na nb nc text))
    (trace (recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a))))
    (uniq-orig nb))
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

(defskeleton isoreject
  (vars (na nb nc text) (a b name))
  (defstrand resp 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig nb)
  (traces
    ((recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a)))))
  (label 0)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton isoreject
  (vars (na nb nc na-0 text) (a b name))
  (defstrand resp 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (defstrand init 3 (na na-0) (nb nb) (nc nc) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-orig nb)
  (operation encryption-test (added-strand init 3)
    (enc nc nb b (privk a)) (0 2))
  (traces
    ((recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a))))
    ((send (cat a na-0)) (recv (enc nb na-0 a (privk b)))
      (send (enc nc nb b (privk a)))))
  (label 1)
  (parent 0)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton isoreject
  (vars (na nb nc text) (a b name))
  (defstrand resp 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (defstrand resp 2 (na nb) (nb nc) (a b) (b a))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-orig nb nc)
  (operation encryption-test (added-strand resp 2)
    (enc nc nb b (privk a)) (0 2))
  (traces
    ((recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a))))
    ((recv (cat b nb)) (send (enc nc nb b (privk a)))))
  (label 2)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (na na) (nb nb) (nc nc))))
  (origs (nc (1 1)) (nb (0 1))))

(defskeleton isoreject
  (vars (na nb nc text) (a b name))
  (defstrand resp 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (defstrand init 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-orig nb)
  (operation encryption-test (displaced 2 0 resp 2)
    (enc nb na-0 a (privk b)) (1 1))
  (traces
    ((recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a))))
    ((send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a)))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (na na) (nb nb) (nc nc))))
  (origs (nb (0 1))))

(comment "Nothing left to do")

(defprotocol isoreject basic
  (defrole init
    (vars (a b name) (na nb nc text))
    (trace (send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a)))))
  (defrole resp
    (vars (a b name) (na nb nc text))
    (trace (recv (cat a na)) (send (enc nb na a (privk b)))
      (recv (enc nc nb b (privk a))))
    (uniq-orig nb))
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

(defskeleton isoreject
  (vars (na nb nc text) (b a name))
  (defstrand init 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (non-orig (privk b))
  (traces
    ((send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a)))))
  (label 4)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton isoreject
  (vars (na nb nc na-0 text) (b a name))
  (defstrand init 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (defstrand init 3 (na na-0) (nb na) (nc nb) (a b) (b a))
  (precedes ((1 2) (0 1)))
  (non-orig (privk b))
  (operation encryption-test (added-strand init 3)
    (enc nb na a (privk b)) (0 1))
  (traces
    ((send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a))))
    ((send (cat b na-0)) (recv (enc na na-0 b (privk a)))
      (send (enc nb na a (privk b)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((b b) (a a) (na na) (nb nb) (nc nc))))
  (origs))

(defskeleton isoreject
  (vars (na nb nc text) (b a name))
  (defstrand init 3 (na na) (nb nb) (nc nc) (a a) (b b))
  (defstrand resp 2 (na na) (nb nb) (a a) (b b))
  (precedes ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig nb)
  (operation encryption-test (added-strand resp 2)
    (enc nb na a (privk b)) (0 1))
  (traces
    ((send (cat a na)) (recv (enc nb na a (privk b)))
      (send (enc nc nb b (privk a))))
    ((recv (cat a na)) (send (enc nb na a (privk b)))))
  (label 6)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((b b) (a a) (na na) (nb nb) (nc nc))))
  (origs (nb (1 1))))

(comment "Nothing left to do")
