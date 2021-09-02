(comment "CPSA 4.3.0")
(comment "All input read from tst/ab.scm")

(defprotocol ab basic
  (defrole init
    (vars (x text) (k skey))
    (trace (send (enc x k)) (recv (enc x x k)))
    (non-orig k)
    (uniq-orig x))
  (defrole A
    (vars (x text) (k skey))
    (trace (recv (enc "A" x k)) (send (enc x x k))))
  (defrole B
    (vars (x text) (k skey))
    (trace (recv (enc "B" x k)) (send (enc x x k))))
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

(defskeleton ab
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (non-orig k)
  (uniq-orig x)
  (traces ((send (enc x k)) (recv (enc x x k))))
  (label 0)
  (unrealized (0 1))
  (origs (x (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton ab
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (defstrand A 2 (k k) (x x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand A 2) (enc x x k) (0 1))
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "A" x k)) (send (enc x x k))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton ab
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (defstrand B 2 (k k) (x x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand B 2) (enc x x k) (0 1))
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "B" x k)) (send (enc x x k))))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
