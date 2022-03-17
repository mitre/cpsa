(herald "Hashtest")

(comment "CPSA 4.3.1")
(comment "All input read from tst/hashtest-key-hash.scm")

(defprotocol hashtest basic
  (defrole init
    (vars (n data) (k akey))
    (trace (send (enc n k)) (recv (enc "h" n)))
    (non-orig (invk k))
    (uniq-orig n))
  (defrole resp
    (vars (k akey) (n data))
    (trace (recv (enc n k)) (send (enc "h" n))))
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

(defskeleton hashtest
  (vars (n data) (k akey))
  (defstrand init 2 (n n) (k k))
  (non-orig (invk k))
  (uniq-orig n)
  (traces ((send (enc n k)) (recv (enc "h" n))))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton hashtest
  (vars (n data) (k k-0 akey))
  (defstrand init 2 (n n) (k k))
  (defstrand resp 2 (n n) (k k-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n)
  (operation encryption-test (added-strand resp 2) (enc "h" n) (0 1))
  (traces ((send (enc n k)) (recv (enc "h" n)))
    ((recv (enc n k-0)) (send (enc "h" n))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton hashtest
  (vars (n data) (k akey))
  (defstrand init 2 (n n) (k k))
  (deflistener n)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n)
  (operation encryption-test (added-listener n) (enc "h" n) (0 1))
  (traces ((send (enc n k)) (recv (enc "h" n))) ((recv n) (send n)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton hashtest
  (vars (n data) (k akey))
  (defstrand init 2 (n n) (k k))
  (defstrand resp 2 (n n) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n)
  (operation nonce-test (contracted (k-0 k)) n (1 0) (enc n k))
  (traces ((send (enc n k)) (recv (enc "h" n)))
    ((recv (enc n k)) (send (enc "h" n))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((n n) (k k))))
  (origs (n (0 0))))

(comment "Nothing left to do")
