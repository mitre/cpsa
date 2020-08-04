(comment "CPSA 4.2.3")
(comment "All input read from tst/weird.scm")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
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

(defskeleton weird
  (vars (a name) (k skey))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (a a) (k k))
  (uniq-orig k)
  (traces ((send k)) ((send (enc a k))))
  (label 0)
  (unrealized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(comment "Nothing left to do")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
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

(defskeleton weird
  (vars (a name) (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (a a) (k k))
  (uniq-orig k)
  (traces ((send k)) ((recv (enc a k))))
  (label 1)
  (unrealized (1 0))
  (origs (k (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton weird
  (vars (a name) (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (a a) (k k))
  (defstrand guesser 1 (a a) (k k))
  (precedes ((2 0) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-strand guesser 1) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((send (enc a k))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(defskeleton weird
  (vars (a name) (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (a a) (k k))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-listener k) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((recv k) (send k)))
  (label 3)
  (parent 1)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton weird
  (vars (a name) (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (a a) (k k))
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (operation generalization deleted (2 0))
  (traces ((send k)) ((recv (enc a k))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(comment "Nothing left to do")
