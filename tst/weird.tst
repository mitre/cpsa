(comment "CPSA 4.3.0")
(comment "All input read from tst/weird.scm")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
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

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (k k) (a a))
  (uniq-orig k)
  (traces ((send k)) ((send (enc a k))))
  (label 0)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(comment "Nothing left to do")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
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

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (uniq-orig k)
  (traces ((send k)) ((recv (enc a k))))
  (label 1)
  (unrealized (1 0))
  (origs (k (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (defstrand guesser 1 (k k) (a a))
  (precedes ((2 0) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-strand guesser 1) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((send (enc a k))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-listener k) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((recv k) (send k)))
  (label 3)
  (parent 1)
  (realized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (operation generalization deleted (2 0))
  (traces ((send k)) ((recv (enc a k))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0))))

(comment "Nothing left to do")
