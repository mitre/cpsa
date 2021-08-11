(herald pfs-via-pubkey)

(comment "CPSA 4.3.0")
(comment "All input read from tst/pfs-via-pubkey.scm")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
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

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey akey))
  (defstrand init 3 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (label 0)
  (unrealized (0 1))
  (origs ((privk "sgn" a) (0 2)) (new-akey (0 0)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey new-akey-0 akey))
  (defstrand init 3 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (operation encryption-test (added-strand resp 2)
    (enc a n s (privk "sgn" b)) (0 1))
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a)))
    ((recv (enc a b new-akey-0 n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey-0))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey akey))
  (defstrand init 3 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk new-akey) (privk "sgn" b))
  (uniq-orig n new-akey (privk "sgn" a))
  (operation encryption-test (displaced 2 0 init 1)
    (enc a b new-akey-0 n (privk "sgn" a)) (1 0))
  (traces
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a)))
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((new-akey new-akey) (a a) (b b) (n n) (s s))))
  (origs ((privk "sgn" a) (0 2)) (new-akey (0 0)) (n (0 0))))

(comment "Nothing left to do")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
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

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (non-orig (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
  (label 3)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pfs-easy
  (vars (s text) (n data) (a b name) (new-akey akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand init 1 (n n) (a a) (b b) (new-akey new-akey))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sgn" a))
  (operation encryption-test (added-strand init 1)
    (enc a b new-akey n (privk "sgn" a)) (0 0))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((new-akey new-akey) (a a) (b b) (n n) (s s))))
  (origs))

(comment "Nothing left to do")

(defprotocol pfs-easy basic
  (defrole init
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))))
  (defrole resp
    (vars (new-akey akey) (a b name) (n data) (s text))
    (trace (recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey))))
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

(defskeleton pfs-easy
  (vars (s s-0 text) (n data) (a b name) (new-akey akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand init 3 (s s-0) (n n) (a a) (b b) (new-akey new-akey))
  (deflistener s)
  (precedes ((1 0) (0 0)))
  (non-orig (invk new-akey))
  (uniq-orig s (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s-0 (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))) ((recv s) (send s)))
  (label 5)
  (unrealized (2 0))
  (preskeleton)
  (origs ((privk "sgn" a) (1 2)) (s (0 1)))
  (comment "Not a skeleton"))

(defskeleton pfs-easy
  (vars (s s-0 text) (n data) (a b name) (new-akey akey))
  (defstrand resp 2 (s s) (n n) (a a) (b b) (new-akey new-akey))
  (defstrand init 3 (s s-0) (n n) (a a) (b b) (new-akey new-akey))
  (deflistener s)
  (precedes ((0 1) (2 0)) ((1 0) (0 0)))
  (non-orig (invk new-akey))
  (uniq-orig s (privk "sgn" a))
  (traces
    ((recv (enc a b new-akey n (privk "sgn" a)))
      (send (enc (enc a n s (privk "sgn" b)) new-akey)))
    ((send (enc a b new-akey n (privk "sgn" a)))
      (recv (enc (enc a n s-0 (privk "sgn" b)) new-akey))
      (send (privk "sgn" a))) ((recv s) (send s)))
  (label 6)
  (parent 5)
  (unrealized (2 0))
  (dead)
  (origs ((privk "sgn" a) (1 2)) (s (0 1)))
  (comment "empty cohort"))

(comment "Nothing left to do")
