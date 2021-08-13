(comment "CPSA 4.3.0")
(comment "All input read from tst/targetterms8.scm")

(defprotocol targetterms8 basic
  (defrole init
    (vars (a name) (n1 n2 text) (k akey))
    (trace (send (enc n1 (enc a n2 k) k)) (recv (enc a n1 k)))
    (non-orig (invk k))
    (uniq-orig n1))
  (defrole resp
    (vars (n1 text) (m mesg) (k akey))
    (trace (recv (enc n1 (enc m k) k)) (send (enc m k))))
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

(defskeleton targetterms8
  (vars (n1 n2 text) (k akey) (a name))
  (defstrand init 2 (n1 n1) (n2 n2) (k k) (a a))
  (non-orig (invk k))
  (uniq-orig n1)
  (traces ((send (enc n1 (enc a n2 k) k)) (recv (enc a n1 k))))
  (label 0)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms8
  (vars (n2 text) (k akey) (a name))
  (defstrand init 2 (n1 n2) (n2 n2) (k k) (a a))
  (non-orig (invk k))
  (uniq-orig n2)
  (operation nonce-test (displaced 1 0 init 1) n1 (0 1)
    (enc n1 (enc a n2 k) k))
  (traces ((send (enc n2 (enc a n2 k) k)) (recv (enc a n2 k))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs (n2 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms8
  (vars (n2 text) (k akey) (a name))
  (defstrand init 2 (n1 n2) (n2 n2) (k k) (a a))
  (defstrand resp 2 (m (cat a n2)) (n1 n2) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n2)
  (operation nonce-test (added-strand resp 2) n2 (0 1)
    (enc n2 (enc a n2 k) k))
  (traces ((send (enc n2 (enc a n2 k) k)) (recv (enc a n2 k)))
    ((recv (enc n2 (enc a n2 k) k)) (send (enc a n2 k))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (n1 n2) (n2 n2) (k k))))
  (origs (n2 (0 0))))

(comment "Nothing left to do")

(defprotocol targetterms8 basic
  (defrole init
    (vars (a name) (n1 n2 text) (k akey))
    (trace (send (enc n1 (enc a n2 k) k)) (recv (enc a n1 k)))
    (non-orig (invk k))
    (uniq-orig n1))
  (defrole resp
    (vars (n1 text) (m mesg) (k akey))
    (trace (recv (enc n1 (enc m k) k)) (send (enc m k))))
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

(defskeleton targetterms8
  (vars (n1 text) (k akey) (a name))
  (defstrand init 2 (n1 n1) (n2 n1) (k k) (a a))
  (non-orig (invk k))
  (uniq-orig n1)
  (traces ((send (enc n1 (enc a n1 k) k)) (recv (enc a n1 k))))
  (label 3)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms8
  (vars (n1 text) (k akey) (a name))
  (defstrand init 2 (n1 n1) (n2 n1) (k k) (a a))
  (defstrand resp 2 (m (cat a n1)) (n1 n1) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 (enc a n1 k) k))
  (traces ((send (enc n1 (enc a n1 k) k)) (recv (enc a n1 k)))
    ((recv (enc n1 (enc a n1 k) k)) (send (enc a n1 k))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (n1 n1) (k k))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")
