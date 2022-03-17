(comment "CPSA 4.3.1")
(comment "All input read from tst/missing_contraction.scm")

(defprotocol missing-contraction basic
  (defrole sender
    (vars (m n text) (a b name))
    (trace (send (enc a m (pubk a))) (send (enc a n (pubk b)))))
  (defrole receiver
    (vars (m text) (a b name))
    (trace (recv (enc a m (pubk b)))))
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

(defskeleton missing-contraction
  (vars (m n text) (a c b name))
  (defstrand sender 2 (m m) (n n) (a a) (b b))
  (defstrand receiver 1 (m m) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a))
  (uniq-orig m)
  (traces ((send (enc a m (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a m (pubk c)))))
  (label 0)
  (unrealized (1 0))
  (origs (m (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton missing-contraction
  (vars (m n text) (a b name))
  (defstrand sender 2 (m m) (n n) (a a) (b b))
  (defstrand receiver 1 (m m) (a a) (b a))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a))
  (uniq-orig m)
  (operation nonce-test (contracted (c a)) m (1 0) (enc a m (pubk a)))
  (traces ((send (enc a m (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a m (pubk a)))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((m m) (a a) (c a) (n n) (b b))))
  (origs (m (0 0))))

(defskeleton missing-contraction
  (vars (n text) (a c b name))
  (defstrand sender 2 (m n) (n n) (a a) (b b))
  (defstrand receiver 1 (m n) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (displaced 2 0 sender 2) m (1 0)
    (enc a m (pubk a)))
  (traces ((send (enc a n (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a n (pubk c)))))
  (label 2)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((m n) (a a) (c c) (n n) (b b))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol missing-contraction basic
  (defrole sender
    (vars (m n text) (a b name))
    (trace (send (enc a m (pubk a))) (send (enc a n (pubk b)))))
  (defrole receiver
    (vars (m text) (a b name))
    (trace (recv (enc a m (pubk b)))))
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

(defskeleton missing-contraction
  (vars (m text) (a c name))
  (defstrand sender 1 (m m) (a a))
  (deflistener (enc a m (pubk c)))
  (non-orig (privk a))
  (uniq-orig m)
  (traces ((send (enc a m (pubk a))))
    ((recv (enc a m (pubk c))) (send (enc a m (pubk c)))))
  (label 3)
  (unrealized (1 0))
  (preskeleton)
  (origs (m (0 0)))
  (comment "Not a skeleton"))

(defskeleton missing-contraction
  (vars (m text) (a c name))
  (defstrand sender 1 (m m) (a a))
  (deflistener (enc a m (pubk c)))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a))
  (uniq-orig m)
  (traces ((send (enc a m (pubk a))))
    ((recv (enc a m (pubk c))) (send (enc a m (pubk c)))))
  (label 4)
  (parent 3)
  (unrealized (1 0))
  (origs (m (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton missing-contraction
  (vars (m text) (a name))
  (defstrand sender 1 (m m) (a a))
  (deflistener (enc a m (pubk a)))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a))
  (uniq-orig m)
  (operation nonce-test (contracted (c a)) m (1 0) (enc a m (pubk a)))
  (traces ((send (enc a m (pubk a))))
    ((recv (enc a m (pubk a))) (send (enc a m (pubk a)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0 1) ((m m) (a a) (c a))))
  (origs (m (0 0))))

(defskeleton missing-contraction
  (vars (m text) (c a b name))
  (deflistener (enc a m (pubk c)))
  (defstrand sender 2 (m m) (n m) (a a) (b b))
  (precedes ((1 1) (0 0)))
  (non-orig (privk a))
  (uniq-orig m)
  (operation nonce-test (displaced 0 2 sender 2) m-0 (1 0)
    (enc a-0 m-0 (pubk a-0)))
  (traces ((recv (enc a m (pubk c))) (send (enc a m (pubk c))))
    ((send (enc a m (pubk a))) (send (enc a m (pubk b)))))
  (label 6)
  (parent 4)
  (realized)
  (shape)
  (maps ((1 0) ((m m) (a a) (c c))))
  (origs (m (1 0))))

(comment "Nothing left to do")

(defprotocol missing-contraction basic
  (defrole sender
    (vars (m n text) (a b name))
    (trace (send (enc a m (pubk a))) (send (enc a n (pubk b)))))
  (defrole receiver
    (vars (m text) (a b name))
    (trace (recv (enc a m (pubk b)))))
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

(defskeleton missing-contraction
  (vars (m n text) (a b c name))
  (defstrand sender 2 (m m) (n n) (a a) (b b))
  (defstrand receiver 1 (m m) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig m)
  (traces ((send (enc a m (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a m (pubk c)))))
  (label 7)
  (unrealized (1 0))
  (origs (m (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton missing-contraction
  (vars (m n text) (a b name))
  (defstrand sender 2 (m m) (n n) (a a) (b b))
  (defstrand receiver 1 (m m) (a a) (b a))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig m)
  (operation nonce-test (contracted (c a)) m (1 0) (enc a m (pubk a)))
  (traces ((send (enc a m (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a m (pubk a)))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((m m) (a a) (b b) (c a) (n n))))
  (origs (m (0 0))))

(defskeleton missing-contraction
  (vars (n text) (a b c name))
  (defstrand sender 2 (m n) (n n) (a a) (b b))
  (defstrand receiver 1 (m n) (a a) (b c))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n)
  (operation nonce-test (displaced 2 0 sender 2) m (1 0)
    (enc a m (pubk a)))
  (traces ((send (enc a n (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a n (pubk c)))))
  (label 9)
  (parent 7)
  (unrealized (1 0))
  (origs (n (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton missing-contraction
  (vars (n text) (a b name))
  (defstrand sender 2 (m n) (n n) (a a) (b b))
  (defstrand receiver 1 (m n) (a a) (b a))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n)
  (operation nonce-test (contracted (c a)) n (1 0) (enc a n (pubk a))
    (enc a n (pubk b)))
  (traces ((send (enc a n (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a n (pubk a)))))
  (label 10)
  (parent 9)
  (seen 8)
  (realized)
  (origs (n (0 0)))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton missing-contraction
  (vars (n text) (a b name))
  (defstrand sender 2 (m n) (n n) (a a) (b b))
  (defstrand receiver 1 (m n) (a a) (b b))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n)
  (operation nonce-test (contracted (c b)) n (1 0) (enc a n (pubk a))
    (enc a n (pubk b)))
  (traces ((send (enc a n (pubk a))) (send (enc a n (pubk b))))
    ((recv (enc a n (pubk b)))))
  (label 11)
  (parent 9)
  (realized)
  (shape)
  (maps ((0 1) ((m n) (a a) (b b) (c b) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")
