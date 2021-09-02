(comment "CPSA 4.3.0")
(comment "All input read from tst/pruning1.scm")

(defprotocol prune basic
  (defrole init
    (vars (a b name) (n text))
    (trace (send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (k akey))
    (trace (recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
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
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (comment "Shows a failure with generalization"
    "Run this with a step count of 4"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a)))))
  (label 0)
  (unrealized (0 1) (0 2))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (k akey) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (k k) (a a))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 1) (enc n (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (k (pubk b)) (a a))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (k (pubk b))) n (0 1)
    (enc n (pubk a)) (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (k akey) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (k (pubk b)) (a a))
  (defstrand trans 3 (n n) (k k) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 2) (enc n (pubk a))
    (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (label 3)
  (parent 2)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (k (pubk b)) (a a))
  (defstrand trans 3 (n n) (k (privk b)) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (k (privk b))) n (0 2)
    (enc n (pubk a)) (enc n (privk b) (pubk a))
    (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (privk b))
      (send (enc n (privk b) (pubk a)))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol prune basic
  (defrole init
    (vars (a b name) (n text))
    (trace (send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (k akey))
    (trace (recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
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
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (comment "Shows a failure with generalization"
    "Run this with a step count of 4"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (k (pubk b)) (a a))
  (defstrand trans 3 (n n) (k (privk b)) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (privk b))
      (send (enc n (privk b) (pubk a)))))
  (label 5)
  (unrealized)
  (shape)
  (maps ((0 1 2) ((n n) (a a) (b b))))
  (origs (n (0 0))))

(comment "Nothing left to do")
