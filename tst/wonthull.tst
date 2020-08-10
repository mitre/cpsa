(herald wonthull (bound 9))

(comment "CPSA 4.3.0")
(comment "All input read from tst/wonthull.scm")
(comment "Strand count bounded at 9")

(defprotocol wonthull basic
  (defrole init
    (vars (a name) (x1 x2 x3 x4 text))
    (trace (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    (non-orig (privk a))
    (uniq-orig x1 x2 x3))
  (defrole resp
    (vars (a name) (y1 y2 y3 text))
    (trace (recv (enc y1 y2 (pubk a)))
      (send (enc "okay" y3 y1 (pubk a)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wonthull
  (vars (x1 x2 x3 x4 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x3) (x4 x4) (a a))
  (non-orig (privk a))
  (uniq-orig x1 x2 x3)
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a)))))
  (label 0)
  (unrealized (0 1))
  (origs (x3 (0 0)) (x2 (0 0)) (x1 (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (displaced 1 0 init 1) x3 (0 1)
    (enc x3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs (x1 (0 0)) (x2 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x3 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x3) (x4 x4) (a a))
  (defstrand resp 2 (y1 x3) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2 x3)
  (operation nonce-test (added-strand resp 2) x3 (0 1)
    (enc x3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    ((recv (enc x3 x2 (pubk a))) (send (enc "okay" y3 x3 (pubk a)))))
  (label 2)
  (parent 0)
  (seen 3)
  (unrealized (0 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (added-strand resp 2) x2 (0 1)
    (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a)))))
  (label 3)
  (parent 1)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 y3) (x4 y3) (a a))
  (defstrand resp 2 (y1 y3) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2 y3)
  (operation nonce-test (contracted (x3 y3) (x4 y3)) y3 (0 1)
    (enc "okay" y3 y3 (pubk a)) (enc y3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc y3 x2 (pubk a))))
      (recv (enc "okay" y3 y3 (pubk a))))
    ((recv (enc y3 x2 (pubk a))) (send (enc "okay" y3 y3 (pubk a)))))
  (label 4)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (x1 x1) (x2 x2) (x3 y3) (x4 y3))))
  (origs (y3 (0 0)) (x2 (0 0)) (x1 (0 0))))

(defskeleton wonthull
  (vars (x1 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 y3) (x3 y3) (x4 y3) (a a))
  (defstrand resp 2 (y1 y3) (y2 y3) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 y3)
  (operation nonce-test (contracted (x2 y3) (x4 y3)) y3 (0 1)
    (enc "okay" y3 y3 (pubk a)) (enc x1 y3 (pubk a))
    (enc y3 y3 (pubk a)))
  (traces
    ((send (cat (enc x1 y3 (pubk a)) (enc y3 y3 (pubk a))))
      (recv (enc "okay" y3 y3 (pubk a))))
    ((recv (enc y3 y3 (pubk a))) (send (enc "okay" y3 y3 (pubk a)))))
  (label 5)
  (parent 3)
  (seen 4)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 x2) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (added-strand resp 2) x2 (0 1)
    (enc "okay" y3 x2 (pubk a)) (enc x1 x2 (pubk a))
    (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" x2 x2 (pubk a)))))
  (label 6)
  (parent 3)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x2) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 x2) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (contracted (x4 x2)) x2 (0 1)
    (enc "okay" x2 x2 (pubk a)) (enc "okay" y3 x2 (pubk a))
    (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" x2 x2 (pubk a)))))
  (label 7)
  (parent 6)
  (seen 5)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol wonthull basic
  (defrole init
    (vars (a name) (x1 x2 x3 x4 text))
    (trace (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    (non-orig (privk a))
    (uniq-orig x1 x2 x3))
  (defrole resp
    (vars (a name) (y1 y2 y3 text))
    (trace (recv (enc y1 y2 (pubk a)))
      (send (enc "okay" y3 y1 (pubk a)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wonthull
  (vars (x1 x3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x3) (x3 x3) (x4 x1) (a a))
  (defstrand resp 2 (y1 x1) (y2 x3) (y3 x3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x3)
  (traces
    ((send (cat (enc x1 x3 (pubk a)) (enc x3 x3 (pubk a))))
      (recv (enc "okay" x3 x1 (pubk a))))
    ((recv (enc x1 x3 (pubk a))) (send (enc "okay" x3 x1 (pubk a)))))
  (label 8)
  (unrealized)
  (shape)
  (maps ((0 1) ((a a) (x1 x1) (x3 x3))))
  (origs (x3 (0 0)) (x1 (0 0))))

(comment "Nothing left to do")
